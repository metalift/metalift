import argparse
import os
from pathlib import Path

from openai import OpenAI

from tenspiler.llm.parser import check_solution
from tenspiler.llm.scripts.utils import (
    extract_and_write,
    get_inv_choice,
    get_num_inv_funcs,
    get_ps_choice,
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
):
    fanout_dir = (
        BENCHMARKS_PATH
        / "outputs"
        / "openai"
        / "end_to_end"
        / f"{fanout}_fanout"
        / benchmark_suite
    )
    ps_output_dir = fanout_dir / "ps"
    inv_output_dir = fanout_dir / "inv"
    ps_output_dir.mkdir(parents=True, exist_ok=True)
    inv_output_dir.mkdir(parents=True, exist_ok=True)

    for ps_idx in range(fanout):
        ps_choice = get_ps_choice(
            client=client,
            source_code=source_code,
            dsl_code=dsl_code,
        )
        ps_sol = extract_and_write(
            ps_choice, ps_output_dir / f"{benchmark_name}_{ps_idx}.txt"
        )
        print(f"Generated {ps_idx}th PS solution")
        print(ps_sol)
        print("\n\n")

        print("Passing through parser")
        try:
            ps_fn_decls, ps_in_calls = check_solution(ps_sol, 1)
        except Exception as e:
            print(f"Failed to parse the {ps_idx}th PS solution")
            print(e)
            continue

        print(f"Generating invariants for the {ps_idx}th PS solution")
        num_inv_funcs = get_num_inv_funcs(benchmark_name)
        for inv_idx in range(fanout):
            inv_choice = get_inv_choice(
                client=client,
                benchmark_name=benchmark_name,
                ps_solution=ps_sol,
                source_code=source_code,
                dsl_code=dsl_code,
            )

            inv_sol = extract_and_write(
                inv_choice,
                inv_output_dir / f"{benchmark_name}_ps_{ps_idx}_inv_{inv_idx}.txt",
            )
            print(f"Generated {inv_idx}th INV solution for the {ps_idx}th PS solution")
            print(inv_sol)
            print("\n\n")

            print("Passing through parser")
            try:
                inv_fn_decls, inv_in_calls = check_solution(inv_sol, num_inv_funcs)
            except Exception as e:
                print(
                    f"Failed to parse the {inv_idx}th INV solution for the {ps_idx}th PS solution"
                )
                print(e)
                continue

            # Send to verifier
            print("Sending to verifier")
            # Driver file
            verification_success = verify_benchmark(
                benchmark_name=benchmark_name,
                synthesized_fn_decls=[*ps_fn_decls, *inv_fn_decls],
                in_calls=[*ps_in_calls, *inv_in_calls],
            )
            if verification_success:
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
    )
