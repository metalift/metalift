import argparse
import json
import os
import time
from pathlib import Path

import anthropic
from openai import OpenAI

from tenspiler.llm.parser import check_solution
from tenspiler.llm.scripts.utils import (
    analyze_benchmark,
    extract,
    extract_and_save,
    get_inv_and_ps,
    get_inv_choice_and_save_prompt,
    get_num_inv_funcs,
    get_ps_choice_and_save_prompt,
    verify_benchmark,
)

# Global variables
TEMPLATE_SYS = "You are a helpful expert in programming languages."
TENSPILER_LLM_PATH = Path(__file__).parent.parent.resolve()
BENCHMARKS_PATH = TENSPILER_LLM_PATH / "benchmarks"
openai_client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
claude_client = anthropic.Anthropic(
    # defaults to os.environ.get("ANTHROPIC_API_KEY")
    api_key=os.getenv("CLAUDE_API_KEY"),
)


# TODO(jie): add type
def run_end_to_end_llm(
    benchmark_suite: str,
    benchmark_name: str,
    source_code: str,
    dsl_code: str,
    fanout: int = 10,
    use_ps_json_file: bool = False,
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

    ps_output_dir = fanout_dir / "ps"
    inv_output_dir = fanout_dir / "inv"
    inv_ps_output_dir = fanout_dir / "inv_ps"
    ps_output_dir.mkdir(parents=True, exist_ok=True)
    inv_output_dir.mkdir(parents=True, exist_ok=True)
    inv_ps_output_dir.mkdir(parents=True, exist_ok=True)

    # Analyze the benchmark
    analyze_time_start = time.time()
    driver = analyze_benchmark(benchmark_name)
    analyze_time_end = time.time()
    print(f"Analyze took {analyze_time_end - analyze_time_start}s")
    incorrect_ps_inv_sols = set()
    ps_inv_sols_seen = set()
    count = 0
    total_time = analyze_time_end - analyze_time_start
    while True:
        if count == 5:
            exit(0)
        print("Generating 10 INV AND PS solutions")
        inv_ps_choices, call_time = get_inv_and_ps(
            client=openai_client,
            benchmark_name=benchmark_name,
            source_code=source_code,
            dsl_code=dsl_code,
            # Prompt is the same for all PS solutions
            output_file=ps_output_dir / f"{benchmark_name}_ps_inv_prompt.json",
            prev_incorrect_sols=incorrect_ps_inv_sols,
        )
        total_time += call_time
        inv_ps_sols = extract_and_save(
            inv_ps_choices, ps_output_dir / f"{benchmark_name}_ps.json"
        )
        for i in range(10):
            print(f"{count * 10 + i}th INV AND PS solution")
            print(inv_ps_sols[i])
            if inv_ps_sols[i] in ps_inv_sols_seen:
                ps_inv_sols_seen.add(inv_ps_sols[i])
                print("INV AND PS solution seen, continuing")

            parse_start_time = time.time()
            try:
                check_solution(inv_ps_sols[i], 1 + get_num_inv_funcs(benchmark_name))
                incorrect_ps_inv_sols.add(inv_ps_sols[i])
            except Exception as e:
                print("failed to parse", e)
                parse_end_time = time.time()
                print(f"Parse took {parse_end_time - parse_start_time}s")
                total_time += parse_end_time - parse_start_time
                print("total time to date", total_time)
                continue
            parse_end_time = time.time()
            print(f"Parse took {parse_end_time - parse_start_time}s")
            total_time += parse_end_time - parse_start_time
            print("total time to date", total_time)

        count += 1

    incorrect_ps_sols = set()
    ps_solutions_seen = set()

    while True:
        for ps_idx in range(fanout):
            if use_ps_json_file:
                json_filename = (
                    BENCHMARKS_PATH
                    / benchmark_suite
                    / "outputs"
                    / "openai"
                    / "ps_100_choices_final"
                    / f"{benchmark_name}.json"
                )
                with open(json_filename) as f:
                    all_sols = json.load(f)
                    ps_choices = extract(all_sols[ps_idx])
            else:
                ps_choices = get_ps_choice_and_save_prompt(
                    client=claude_client,
                    source_code=source_code,
                    dsl_code=dsl_code,
                    # Prompt is the same for all PS solutions
                    output_file=ps_output_dir / f"{benchmark_name}_ps_prompt.json",
                    prev_incorrect_sols=incorrect_ps_sols,
                )
                ps_sols = extract_and_save(
                    ps_choices, ps_output_dir / f"{benchmark_name}_ps.json"
                )
                ps_sol = ps_sols[0]
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
            import pdb

            pdb.set_trace()
            if os.getenv("SKIP_INV"):
                incorrect_ps_sols.add(ps_sol)
                continue

            print(f"Generating invariants for the {ps_idx}th PS solution")
            inv_solutions_seen = set()
            incorrect_inv_sols = set()

            import pdb

            pdb.set_trace()
            for inv_idx in range(fanout):
                num_inv_funcs = get_num_inv_funcs(benchmark_name)
                inv_choices = get_inv_choice_and_save_prompt(
                    client=claude_client,
                    benchmark_name=benchmark_name,
                    ps_solution=ps_sol,
                    source_code=source_code,
                    dsl_code=dsl_code,
                    # Prompt is the same for all inv solutions generated for one ps solution
                    output_file=inv_output_dir
                    / f"{benchmark_name}_ps_{ps_idx}_inv_prompt.json",
                    prev_incorrect_sols=incorrect_inv_sols,
                )
                inv_sols = extract_and_save(
                    inv_choices,
                    inv_output_dir / f"{benchmark_name}_ps_{ps_idx}_inv.json",
                )
                inv_sol = inv_sols[0]
                print(f"{inv_idx}th INV solution for the {ps_idx}th PS solution")
                print(inv_sol)

                if inv_sol in inv_solutions_seen:
                    print(
                        f"Skipping {inv_idx}th INV solution because it was already seen"
                    )
                    continue
                inv_solutions_seen.add(inv_sol)

                print("Passing through parser")
                try:
                    inv_fn_decls, inv_in_calls = check_solution(inv_sol, num_inv_funcs)
                    print("Passed parser!")
                except Exception as e:
                    inv_sol = "\n".join(
                        [
                            inv_sol,
                            "This solution contains python syntax not supported by the defined functions.",
                        ]
                    )
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
                import pdb

                pdb.set_trace()
                if verification_success:
                    end_time = time.time()
                    print(
                        f"Successfully verified the {inv_idx}th INV solution for the {ps_idx}th PS solution"
                    )
                    print(f"Time taken: {end_time - start_time}s")
                    return
                incorrect_inv_sols.add(inv_sol)


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
    all_suites = {"blend", "llama"}
    benchmark_suite, source_code = None, None
    for file in BENCHMARKS_PATH.rglob("*.cc"):
        if file.name == f"{args.benchmark}.cc":
            with open(file) as f:
                source_code = f.read()
                suite_folder = file.parent.parent
                while suite_folder.name not in all_suites:
                    suite_folder = suite_folder.parent
                benchmark_suite = suite_folder.name
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
