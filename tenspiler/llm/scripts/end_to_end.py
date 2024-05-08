import argparse
import os
from pathlib import Path

from openai import OpenAI

from tenspiler.llm.parser import check_solution
from tenspiler.llm.scripts.utils import (
    extract_and_write,
    get_inv_choices,
    get_num_inv_funcs,
    get_ps_choices,
    verify_solution,
)

# Global variables
TEMPLATE_SYS = "You are a helpful expert in programming languages."
TENSPILER_LLM_PATH = Path(__file__).parent.parent.resolve()
BENCHMARKS_PATH = TENSPILER_LLM_PATH / "benchmarks"
client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))


# TODO(jie): add type
def get_ps(
    benchmark_suite: str,
    benchmark_name: str,
    source_code: str,
    dsl_code: str,
    n_choices: int = 10,
):
    # call the completions endpoint to get the completions for the prompt
    ps_choices = get_ps_choices(
        client=client,
        source_code=source_code,
        dsl_code=source_code,
        n_choices=n_choices,
    )
    ps_output_dir = (
        BENCHMARKS_PATH
        / benchmark_suite
        / "outputs"
        / "end_to_end"
        / "openai"
        / "ps"
        / f"{n_choices}_choices"
    )
    ps_solutions = extract_and_write(
        ps_choices, ps_output_dir / f"{benchmark_name}.json"
    )

    # Now for each ps solution, we try to synthesize invariants
    for ps_idx, ps_solution in enumerate(ps_solutions):
        print(f"Generated {ps_idx}th PS solution")
        print(ps_solution)
        print("\n\n")

        print("Passing through parser")
        try:
            ps_fn_decls, _ = check_solution(ps_solution, 1)
        except Exception as e:
            print(f"Failed to parse the {ps_idx}th PS solution")
            print(e)
            continue
        # TODO(jie): pass through parser

        print(f"Generating invariants for the {ps_idx}th PS solution")
        inv_choices = get_inv_choices(
            client=client,
            benchmark_name=benchmark_name,
            ps_solution=ps_solution,
            source_code=source_code,
            dsl_code=dsl_code,
            n_choices=n_choices,
        )
        inv_output_dir = (
            BENCHMARKS_PATH
            / benchmark_suite
            / "outputs"
            / "end_to_end"
            / "openai"
            / "inv"
            / f"{n_choices}_choices"
        )
        inv_solutions = extract_and_write(
            inv_choices, inv_output_dir / f"{benchmark_name}_ps_{ps_idx}th.json"
        )
        for inv_idx, inv_solution in enumerate(inv_solutions):
            print(f"Generated {inv_idx}th INV solution for the {ps_idx}th PS solution")
            print(inv_solution)
            print("\n\n")

            print("Passing through parser")
            try:
                inv_fn_decls, _ = check_solution(
                    inv_solution, get_num_inv_funcs(benchmark_name)
                )
            except Exception as e:
                print(
                    f"Failed to parse the {inv_idx}th INV solution for the {ps_idx}th PS solution"
                )
                print(e)
                continue

            # Send to verifier
            print("Sending to verifier")
            target_lang = ps_fn_decls + inv_fn_decls
            # Driver file
            verify_solution()


if __name__ == "__main__":
    # Set up some global variables / paths

    # reading arguments from the command line
    parser = argparse.ArgumentParser()
    parser.add_argument("--benchmark", type=str)
    parser.add_argument(
        "--dsl-code", type=str, default=str(TENSPILER_LLM_PATH / "python_dsl.py")
    )
    parser.add_argument("--n-choices", type=int, default=10)
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

    print(source_code)
    exit(0)
    files = list(filter(lambda x: x.is_file(), BENCHMARKS_PATH.rglob("*.cc")))
    print(files[0].name)
    # import pdb; pdb.set_trace()

    dir = f"./benchmarks/{args.benchmark_suite}/outputs/openai/ps/{args.n_choices}_choices"
    filename = args.filename
    source_code = open(args.source_code).read()
    dsl_code = open(args.dsl_code).read()
