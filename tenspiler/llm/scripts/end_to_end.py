import argparse
import os
from pathlib import Path
import json
import time
import shutil

from openai import OpenAI

from metalift.frontend.llvm import Driver
from tenspiler.llm.parser import check_solution
from tenspiler.llm.scripts.utils import (
    analyze_benchmark,
    extract,
    extract_and_save,
    get_inv_choice_and_save_prompt,
    get_num_inv_funcs,
    get_ps_choice_and_save_prompt,
    verify_benchmark,
)

# Global variables
TEMPLATE_SYS = "You are a helpful expert in programming languages."
TENSPILER_LLM_PATH = Path(__file__).parent.parent.resolve()
BENCHMARKS_PATH = TENSPILER_LLM_PATH / "benchmarks"
client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))


# TODO(jie): add type
def run_end_to_end_llm(
    benchmark_suite: str,
    benchmark_name: str,
    source_code: str,
    dsl_code: str,
    fanout: int = 10,
    use_ps_json_file: bool = False
):
    start_time = time.time()
    fanout_dir = (
        BENCHMARKS_PATH
        / "outputs"
        / "openai"
        / "end_to_end"
        / f"{fanout}_fanout"
        / benchmark_suite
        / benchmark_name
    )
    # Remove all content in this directory
    shutil.rmtree(fanout_dir, ignore_errors=True)

    ps_output_dir = fanout_dir / "ps"
    inv_output_dir = fanout_dir / "inv"
    ps_output_dir.mkdir(parents=True, exist_ok=True)
    inv_output_dir.mkdir(parents=True, exist_ok=True)

    # Analyze the benchmark
    driver = analyze_benchmark(benchmark_name)

    curr_round_incorrect_ps_sols = set()

    while True:
        prev_round_incorrect_ps_sols = curr_round_incorrect_ps_sols
        curr_round_incorrect_ps_sols = set()

        if use_ps_json_file:
            json_filename = BENCHMARKS_PATH / benchmark_suite / "outputs" / "openai" / "ps_100_choices_final" / f"{benchmark_name}.json"
            with open(json_filename) as f:
                all_sols = json.load(f)
                ps_choices = extract(all_sols[ps_idx])
        else:
            import pdb; pdb.set_trace()
            ps_choices = get_ps_choice_and_save_prompt(
                client=client,
                source_code=source_code,
                dsl_code=dsl_code,
                # Prompt is the same for all PS solutions
                output_file=ps_output_dir / f"{benchmark_name}_ps_prompt.json",
                prev_incorrect_sols=prev_round_incorrect_ps_sols,
            )
        ps_sols = extract_and_save(
            ps_choices, ps_output_dir / f"{benchmark_name}_ps.json"
        )
        import pdb; pdb.set_trace()

        ps_solutions_seen = set()

        for ps_idx in range(fanout):
            ps_sol = ps_sols[ps_idx]
            ps_start_time = time.time()

            print(f"{ps_idx}th PS solution")
            print(ps_sol)

            if ps_sol in ps_solutions_seen:
                print(f"Skipping {ps_idx}th PS solution because it was already seen")
                ps_end_time = time.time()
                print(f"PS solution took {ps_end_time - ps_start_time}s")
                continue
            ps_solutions_seen.add(ps_sol)

            print("Passing through parser")
            parser_start_time = time.time()
            try:
                ps_fn_decls, ps_in_calls = check_solution(ps_sol, 1)
                print("Passed parser!")
                parser_end_time = time.time()
                print(f"Parser took {parser_end_time - parser_start_time}s")
            except Exception as e:
                print(f"Failed to parse the {ps_idx}th PS solution")
                print(e)
                ps_end_time = time.time()
                print(f"PS solution took {ps_end_time - ps_start_time}s")
                print(f"Parser took {ps_end_time - parser_start_time}s")
                continue

            ps_end_time = time.time()
            print(f"PS solution took {ps_end_time - ps_start_time}s")
            import pdb; pdb.set_trace()
            if os.getenv("SKIP_INV"):
                curr_round_incorrect_ps_sols.add(ps_sol)
                continue

            print(f"Generating invariants for the {ps_idx}th PS solution")
            inv_solutions_seen = set()
            num_inv_funcs = get_num_inv_funcs(benchmark_name)
            inv_choices = get_inv_choice_and_save_prompt(
                client=client,
                benchmark_name=benchmark_name,
                ps_solution=ps_sol,
                source_code=source_code,
                dsl_code=dsl_code,
                # Prompt is the same for all inv solutions generated for one ps solution
                output_file=inv_output_dir / f"{benchmark_name}_ps_{ps_idx}_inv_prompt.json",
                prev_incorrect_sols=set(),
            )
            inv_sols = extract_and_save(
                inv_choices,
                inv_output_dir / f"{benchmark_name}_ps_{ps_idx}_inv.json",
            )
            import pdb; pdb.set_trace()
            for inv_idx in range(fanout):
                inv_sol = inv_sols[inv_idx]
                print(f"{inv_idx}th INV solution for the {ps_idx}th PS solution")
                print(inv_sol)

                if inv_sol in inv_solutions_seen:
                    print(f"Skipping {inv_idx}th INV solution because it was already seen")
                    continue
                inv_solutions_seen.add(inv_sol)

                print("Passing through parser")
                try:
                    inv_fn_decls, inv_in_calls = check_solution(inv_sol, num_inv_funcs)
                    print("Passed parser!")
                except Exception as e:
                    inv_sol = "\n".join([inv_sol, "This solution contains python syntax not supported by the defined functions."])
                    print(
                        f"Failed to parse the {inv_idx}th INV solution for the {ps_idx}th PS solution"
                    )
                    print(e)
                    continue

                # Send to verifier
                print("Sending to verifier")
                # Driver file
                verification_success = verify_benchmark(
                    driver=driver,
                    benchmark_name=benchmark_name,
                    synthesized_fn_decls=[*ps_fn_decls, *inv_fn_decls],
                    in_calls=[*ps_in_calls, *inv_in_calls],
                )
                if verification_success:
                    end_time = time.time()
                    print(f"Successfully verified the {inv_idx}th INV solution for the {ps_idx}th PS solution")
                    print(f"Time taken: {end_time - start_time}s")
                    return



if __name__ == "__main__":
    # Set up some global variables / paths

    # reading arguments from the command line
    parser = argparse.ArgumentParser()
    parser.add_argument("--benchmark", type=str)
    parser.add_argument(
        "--dsl-code", type=str, default=str(TENSPILER_LLM_PATH / "python_dsl.py")
    )
    parser.add_argument("--fanout", type=int, default=10)
    args = parser.parse_args()

    # First we find the source code
    benchmark_suite, source_code = None, None
    for file in BENCHMARKS_PATH.rglob("*.cc"):
        if file.name == f"{args.benchmark}.cc":
            with open(file) as f:
                source_code = f.read()
                benchmark_suite = file.parent.parent.name

    if source_code is None:
        print(f"Could not find benchmark {args.benchmark}")
        exit(1)

    # Then we find the dsl code
    with open(args.dsl_code) as f:
        dsl_code = f.read()

    print(f"Found benchmark {args.benchmark} in suite {benchmark_suite}")
    print(source_code)
    run_end_to_end_llm(
        benchmark_suite=benchmark_suite,
        benchmark_name=args.benchmark,
        source_code=source_code,
        dsl_code=dsl_code,
        fanout=args.fanout,
        # use_ps_json_file=True
    )
