import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Union

from metalift.frontend.llvm import Driver
from metalift.ir import (
    Axiom,
    Bool,
    Call,
    Eq,
    Expr,
    FnDecl,
    FnDeclRecursive,
    Lit,
    Object,
    Var,
    create_object,
    is_fn_decl_type,
)
from metalift.rosette_translator import generate_vars
from metalift.smt_util import toSMT
from metalift.synthesis_common import get_used_fn_names

INDENTATION = " " * 4
hf_token = os.getenv("HUGGING_FACE_API")
if not hf_token:
    raise ValueError("Please set the environment variable HUGGING_FACE_API")


TEMPLATE_SYS = "You are a helpful expert in programming languages."
TEMPLATE_ERR = "These generated programs are incorrect. Do not generate the same. Please generate another program."
TEMPLATE_ENCLOSE_CODE = "Please enclose your solution in a python code block"

llama_repo = "meta-llama/Meta-Llama-3-8B-Instruct"
mistral_repo = "mistralai/Mistral-Nemo-Instruct-2407"

SYNTHESIS_LOGS_DIR = Path("./synthesisLogs")


def extract_all_python_functions(s: str) -> list[str]:
    # TODO(sahil): use this instead of the extract function in all models.
    extracted_result = [
        x.group(1)
        for x in re.finditer(
            r"```(?:Python|python|assembly|cpp|c|c\+\+)?(.*?)```", s, re.DOTALL
        )
    ]
    return extracted_result


######
# Some helper classes and functions for inv
######
@dataclass
class SingleLoopInfo:
    loop_var: Object
    read_vars: list[Object]
    modified_vars: list[Object]


@dataclass
class DoubleLoopInfo:
    outer_loop_var: Object
    inner_loop_var: Object
    outer_loop_read_vars: list[Object]
    inner_loop_read_vars: list[Object]
    outer_loop_modified_vars: list[Object]
    inner_loop_modified_vars: list[Object]


def replace_in_call(expr: Expr, in_call: tuple[str, str]) -> Expr:
    caller_fn_name, callee_fn_name = in_call
    if (
        isinstance(expr, Call)
        or isinstance(expr, FnDecl)
        or isinstance(expr, FnDeclRecursive)
    ):
        new_args = []
        for arg in expr.arguments():
            if isinstance(arg, FnDecl) or isinstance(arg, FnDeclRecursive):
                if arg.name() == callee_fn_name and expr.name() == caller_fn_name:
                    new_args.append(Var(callee_fn_name, arg.type))
                else:
                    new_args.append(replace_in_call(arg, in_call))
            else:
                new_args.append(replace_in_call(arg, in_call))
        if isinstance(expr, Call):
            return Call(expr.name(), expr.type, *new_args)
        elif isinstance(expr, FnDecl):
            return FnDecl(
                expr.name(),
                expr.returnT(),
                replace_in_call(expr.body(), in_call),
                *new_args,
            )
        else:
            return FnDeclRecursive(
                expr.name(),
                expr.returnT(),
                replace_in_call(expr.body(), in_call),
                *new_args,
            )
    elif isinstance(expr, Var) or isinstance(expr, Lit):
        return expr
    else:
        return expr.map_args(lambda x: replace_in_call(x, in_call))


def replace_in_calls(expr: Expr, in_calls: list[tuple[str, str]]) -> Expr:
    # TODO(jie): add comment
    for in_call in in_calls:
        expr = replace_in_call(expr, in_call)
    return expr


def replace_args(*, args: list[Object], replace_args: dict[str, str]) -> list[Object]:
    """In the given list of args, replace the variable names according to the given `replace_args`."""
    new_args: list[Object] = []
    for arg in args:
        arg_name = replace_args.get(arg.var_name(), arg.var_name())
        new_args.append(create_object(arg.type, arg_name))
    return new_args


def get_inv_args(
    loop_info: SingleLoopInfo | DoubleLoopInfo,
) -> Union[list[Object], tuple[list[Object], list[Object]]]:
    """Given some loop info, return the invariant arguments."""
    if isinstance(loop_info, SingleLoopInfo):
        vars = sorted(
            list(
                set(
                    [var.src for var in loop_info.read_vars]
                    + [var.src for var in loop_info.modified_vars]
                    + [loop_info.loop_var.src]
                )
            ),
            key=lambda x: x.name(),
        )
        return [create_object(var.type, var.name()) for var in vars]
    else:
        outer_inv_args = sorted(
            list(
                set(
                    [var.src for var in loop_info.outer_loop_read_vars]
                    + [var.src for var in loop_info.outer_loop_modified_vars]
                    + [loop_info.outer_loop_var.src]
                )
            ),
            key=lambda x: x.name(),
        )
        inner_inv_args = sorted(
            list(
                set(
                    [var.src for var in loop_info.inner_loop_read_vars]
                    + [var.src for var in loop_info.inner_loop_modified_vars]
                    + [loop_info.inner_loop_var.src]
                )
            ),
            key=lambda x: x.name(),
        )
        outer_inv_args = [create_object(var.type, var.name()) for var in outer_inv_args]
        inner_inv_args = [create_object(var.type, var.name()) for var in inner_inv_args]
        return outer_inv_args, inner_inv_args


def process_ps_fn_decl(
    fn_decl: Union[FnDecl, FnDeclRecursive],
    output_var: Object,
) -> Union[FnDecl, FnDeclRecursive]:
    """Converts the given PS function declaration to the form of output_var == fn_decl.body()."""
    return fn_decl.__class__(
        f"{fn_decl.name()}_ps",
        Bool,
        Eq(output_var.src, fn_decl.body()),
        *fn_decl.arguments(),
        output_var.src,
    )


def process_dsl_fns_for_smt(
    dsl_fns: list[FnDecl | FnDeclRecursive], in_calls: list[tuple[str, str]]
) -> list[FnDecl | FnDeclRecursive]:
    """Process DSL functions for SMT verification.

    This includes removing functions that are already defined in helper SMT files, or functions that
    have lambda functions as arguments but are not used anywhere in the synthesized solutions.
    """
    final_dsl_fns: list[FnDecl | FnDeclRecursive] = []
    for fn_decl in dsl_fns:
        # Skip functions that are already in list-axioms.smt.
        # TODO(jie): this is a bit hacky. We could remove all these functions in list-axioms.smt, but then we need to make sure that they are added to perspective driver files.
        if fn_decl.name().startswith("integer"):
            continue
        if fn_decl.name() in {
            "vec_slice",
            "matrix_col_slice",
            "firsts",
            "rests",
            "matrix_transpose",
            "matrix_row_slice",
        }:
            continue

        # If we have functions in the grammar that takes in lambda functions,
        # but not used anywhere, then we don't include them. This is due to the fact that we inline all these lambda functions, and we can't do so if there is no actual definitions for them.
        all_fns_with_inline_fns = set(in_call[0] for in_call in in_calls)
        if (
            any(is_fn_decl_type(arg.type) for arg in fn_decl.arguments())
            and fn_decl.name() not in all_fns_with_inline_fns
        ):
            continue

        final_dsl_fns.append(fn_decl)
    return final_dsl_fns


def process_dsl_fns_for_rosette(
    dsl_fns: list[FnDecl | FnDeclRecursive],
) -> list[FnDecl | FnDeclRecursive]:
    """Process DSL functions for Rosette verification.

    This includes removing functions that are already defined in utils.rkt, or functions to be synthesized.
    """
    final_dsl_fns: list[FnDecl | FnDeclRecursive] = []
    # write dsl code
    for fn_decl in dsl_fns:
        # Skip some functions that are already in utils.rkt
        # TODO(jie): this is a bit hacky. We could remove all these functions in utils.rkt, but then we need to make sure that they are added to perspective driver files.
        if fn_decl.name().startswith("integer"):
            continue
        if fn_decl.name() in {"firsts"}:
            continue
        if fn_decl.body() is None:
            continue
        final_dsl_fns.append(fn_decl)

    return final_dsl_fns


def process_synthesized_fn_decls(
    *,
    output_var: Object,
    benchmark_name: str,
    synthesized_fn_decls: list[FnDecl | FnDeclRecursive],
) -> None:
    """The functions LLMs return need to be processed before verification.

    For example, in VC the invariants have name {benchmark_name}_inv{number}, but in the synthesized functions they are named "invariant" or "invariant1" and "invariant2".
    Moreover, the PS function name needs to be changed to {benchmark_name}_ps, and the body of the PS function needs to be changed to output_var == body.
    """
    for idx, fn_decl in enumerate(synthesized_fn_decls):
        # Change function names
        # Change single loop invariant names
        if fn_decl.name() == "invariant":
            fn_decl.set_name(f"{benchmark_name}_inv0")

        # Change double loop invariant names
        if fn_decl.name() == "invariant1":
            fn_decl.set_name(f"{benchmark_name}_inv0")
        if fn_decl.name() == "invariant2":
            fn_decl.set_name(f"{benchmark_name}_inv1")

        # Change ps function name
        if fn_decl.name() == benchmark_name:
            fn_decl = process_ps_fn_decl(fn_decl, output_var)
            synthesized_fn_decls[idx] = fn_decl


def verify_benchmark_rosette(
    *,
    driver: Driver,
    benchmark_name: str,
    synthesized_fn_decls: list[Union[FnDecl, FnDeclRecursive]],
    in_calls: list[tuple[str, str]],
    dsl_fns: list[FnDecl | FnDeclRecursive],
    vc: Expr,
    list_bound: int = 2,
    bitwidth: int = 6,
) -> bool:
    """Verify the benchmark using Rosette."""
    bitwuzla_path = os.getenv("BITWUZLA_PATH")
    if bitwuzla_path is None:
        raise Exception("Please set BITWUZLA_PATH")
    print(f"Generating verification file for benchmark {benchmark_name}")

    SYNTHESIS_LOGS_DIR.mkdir(exist_ok=True)

    # Copy over the utils.rkt and bounded.rkt files
    Path(SYNTHESIS_LOGS_DIR / "utils.rkt").write_text(
        Path("metalift/utils/utils.rkt").read_text()
    )
    Path(SYNTHESIS_LOGS_DIR / "bounded.rkt").write_text(
        Path("metalift/utils/bounded.rkt").read_text()
    )
    verify_file_name = SYNTHESIS_LOGS_DIR / f"verify_{benchmark_name}.rkt"
    f = open(verify_file_name, "w")
    print(
        "#lang rosette\n"
        + '(require "./bounded.rkt")\n'
        + '(require "./utils.rkt")\n'
        + "(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)\n"
        + "(require rosette/solver/smt/bitwuzla)\n"
        + f'(current-solver (bitwuzla #:path "{bitwuzla_path}" #:options (hash \':seed 0)))\n'
        + "\n",
        file=f,
    )
    # write dsl code
    for fn_decl in process_dsl_fns_for_rosette(dsl_fns):
        fn_decl = replace_in_calls(fn_decl, in_calls)
        print("\n", fn_decl.to_rosette(), "\n", file=f)

    for fn_decl in synthesized_fn_decls:
        print("\n", replace_in_calls(fn_decl, in_calls).to_rosette(), "\n", file=f)

    # Write variables
    vars = set(driver.var_tracker.all())
    var_decls, _ = generate_vars(vars, list_bound)
    print(var_decls, file=f)

    # Write bitwidth
    print(f"(current-bitwidth {bitwidth})", file=f)

    print(f"(define vc (verify (assert {vc.to_rosette()})))\n", file=f)
    print("vc", file=f)

    f.close()

    # Run the verification
    print(f"Running verification for benchmark {benchmark_name}")
    verification_output = subprocess.run(
        ["racket", verify_file_name], check=True, capture_output=True
    )
    if verification_output.stdout.decode("utf-8").split("\n")[0] == "(unsat)":
        print("Verification successful")
        print("\n\n")
        return True
    else:
        print("Verification failed")
        print(verification_output.stdout.decode("utf-8"))
        print("\n\n")
        return False


def verify_benchmark_smt(
    *,
    driver: Driver,
    benchmark_name: str,
    synthesized_fn_decls: list[Union[FnDecl, FnDeclRecursive]],
    in_calls: list[tuple[str, str]],
    dsl_fns: list[FnDecl | FnDeclRecursive],
    vc: Expr,
    dsl_fn_name_to_axioms: dict[str, list[Axiom]],
) -> None:
    """Verify the benchmark using SMT."""
    SYNTHESIS_LOGS_DIR.mkdir(exist_ok=True)
    verify_file = SYNTHESIS_LOGS_DIR / f"verify_{benchmark_name}.smt"
    final_dsl_fns = process_dsl_fns_for_smt(dsl_fns, in_calls)

    # Find axioms that are needed
    used_fn_names = get_used_fn_names(synthesized_fn_decls)
    axioms: list[Axiom] = []
    for fn_name in used_fn_names:
        axioms.extend(dsl_fn_name_to_axioms.get(fn_name, []))

    synthesized_fn_names = [fn_decl.name() for fn_decl in synthesized_fn_decls]
    target_lang_fn_names = [fn_decl.name() for fn_decl in final_dsl_fns]

    toSMT(
        target_lang=list(set([*final_dsl_fns, *axioms])),
        vars=set(driver.var_tracker.all()),
        inv_and_ps=synthesized_fn_decls,
        preds=[],
        vc=vc,
        out_file=verify_file,
        in_calls=in_calls,
        fn_calls=[*target_lang_fn_names, *synthesized_fn_names],
    )

    # Run external verification subprocess.
    verify_proc = subprocess.run(
        [
            "cvc5",
            "--lang=smt",
            "--produce-models",
            "--tlimit=100000",
            verify_file,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )

    if verify_proc.returncode < 0:
        return False
    else:
        proc_output = verify_proc.stdout
        result_verify = proc_output.decode("utf-8").split("\n")[0]
        print(result_verify)
        return True


# Define the replacement function
def replace_ite(ps_sol: str) -> str:
    """Replace ite() with the Python ternary operator."""

    def repl_func(match):
        cond = match.group(1).strip()
        a = match.group(2).strip()
        b = match.group(3).strip()
        return f"{a} if {cond} else {b}"

    ite_pattern = r"ite\(([^,]+),\s*([^,]+),\s*([^)]+)\)"
    return re.sub(ite_pattern, repl_func, ps_sol)
