import copy
import os
import subprocess
from enum import Enum
from pathlib import Path
from typing import Any, Callable, Optional, Union

import anthropic
import boto3
import google.generativeai as genai
from openai import OpenAI

from llm.constants import (
    BEDROCK_MODEL_ID,
    SYNTHESIS_LOGS_DIR,
    TEMPLATE_ERR,
    TEMPLATE_SYS,
)
from llm.parser import check_solution
from llm.prompts import get_inv_prompt, get_ps_prompt
from llm.utils import (
    NestedLoopInfo,
    SequentialLoopInfo,
    SingleLoopInfo,
    extract_all_python_functions,
    get_inv_args,
    infer_nested_loop_info_from_llvm,
    infer_sequential_loop_info_from_llvm,
    infer_single_loop_info_from_llvm,
    prepare_loop_info_from_driver,
    replace_ite,
)
from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import (
    Axiom,
    Bool,
    Call,
    Eq,
    Expr,
    FnDecl,
    FnDeclRecursive,
    Int,
    Lit,
    Object,
    Var,
    create_object,
    is_fn_decl_type,
)
from metalift.rosette_translator import generate_vars
from metalift.smt_util import augment_arguments, replace_fn_name, toSMT
from metalift.synthesis_common import get_used_fn_names
from metalift.vc_util import and_objects
from tenspiler.constants_vec import TENSPILER_FNS
from tenspiler.tenspiler_common import (
    DISSOLVE_MATRIX_SELECTION_TWO_ARGS,
    DISSOLVE_SELECT_TWO_ARGS_ARG,
    DISSOLVE_SELECTION_TWO_ARGS,
    MATRIX_SELECTION_TWO_ARGS,
    SELECT_TWO_ARGS_ARG,
    SELECTION_TWO_ARGS,
    dissolve_matrix_selection_two_args_fn_decl,
    dissolve_selection_two_args_fn_decl,
)
from tenspiler.tree_parser import (
    find_root_node_from_file,
    get_num_loops,
    get_return_var_name,
    has_nested_loops,
    make_input_variables,
)


class VerificationMethod(Enum):
    NONE = "none"
    ROSETTE = "rosette"
    SMT = "smt"


class LLMModel(Enum):
    CLAUDE = "claude"
    GPT = "gpt"
    GEMINI = "gemini"
    BEDROCK = "bedrock"


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
    for in_call in in_calls:
        expr = replace_in_call(expr, in_call)
    return expr


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
    num_invariants: int = 1,
) -> None:
    """The functions LLMs return need to be processed before verification.

    For example, in VC the invariants have name {benchmark_name}_inv{number}, but in the synthesized functions they are named "invariant" or "invariant1" and "invariant2".
    Moreover, the PS function name needs to be changed to {benchmark_name}_ps, and the body of the PS function needs to be changed to output_var == body.
    """
    for idx, fn_decl in enumerate(synthesized_fn_decls):
        # Change invariant function names:
        # - single loop models often emit `invariant`
        # - multi-loop models typically emit invariant1..invariantN
        if fn_decl.name() == "invariant":
            fn_decl.set_name(f"{benchmark_name}_inv0")
        for inv_idx in range(num_invariants):
            if fn_decl.name() == f"invariant{inv_idx + 1}":
                fn_decl.set_name(f"{benchmark_name}_inv{inv_idx}")

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
    print(f"Verification file: {verify_file_name}")

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
    vc_clauses: list[Expr],
    dsl_fn_name_to_axioms: dict[str, list[Axiom]],
    additional_axioms: list[Axiom],
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
    axioms.extend(additional_axioms)

    synthesized_fn_names = [fn_decl.name() for fn_decl in synthesized_fn_decls]
    target_lang_fn_names = [fn_decl.name() for fn_decl in final_dsl_fns]

    toSMT(
        target_lang=list(set([*final_dsl_fns, *axioms])),
        vars=set(driver.var_tracker.all()),
        inv_and_ps=synthesized_fn_decls,
        preds=[],
        vc_clauses=vc_clauses,
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
            "--incremental",
            verify_file,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )

    if verify_proc.returncode < 0:
        return False
    else:
        proc_output = verify_proc.stdout.decode("utf-8")
        results = [line.strip() for line in proc_output.splitlines() if line.strip()]
        if not results:
            print("unknown")
            return False
        if all(result == "unsat" for result in results):
            print("unsat")
            return True
        print(results[0])
        return False


def run_llm_synthesis_algorithm(
    *,
    driver: Driver,
    loop_info: SingleLoopInfo | NestedLoopInfo | SequentialLoopInfo | None,
    output_var: Object,
    source_code: str,
    fn_name: str,
    llm_model: LLMModel,
    dsl_fns: list[FnDecl | FnDeclRecursive],
    dsl_fn_name_to_axioms: dict[str, list[Axiom]],
    additional_axioms: list[Axiom] = [],
    max_num_ps_sols: int = 10,
    max_num_inv_sols: int = 10,
    verification_method: VerificationMethod = VerificationMethod.SMT,
    list_bound: int = 2,
) -> list[FnDecl | FnDeclRecursive]:
    """
    The flow of the function is as follows:
    1. Start with asking the model to rewrite the function.
    2. Check if solution passes the parser. If it does, proceed. Otherwise, give parser feedback and ask the model to fix the function. Repeat this step for `max_parser_tries` times.
    4. Return the solution. Otherwise, return None.

    we return a list with maximum length of `max_num_tries` and each element containing the following information:
    - solutions: A list of solutions that we tried to pass to parser. Each solution is in the form of (solution, feedback, time_taken) tuple.
    """
    # First we need to get DSL code
    dsl_code = "\n\n".join(fn.to_python() for fn in dsl_fns)

    # First we need to generate prompts
    ps_prompt = get_ps_prompt(
        benchmark_name=fn_name, dsl_code=dsl_code, source_code=source_code
    )

    # Get result from LLM
    ps_sols: list[str] = []
    found_sol = False
    final_synthesized_fn_decls: Optional[list[FnDecl | FnDeclRecursive]] = None
    for ps_sol_index in range(max_num_ps_sols):
        # First we get a new solution. If there are previous incorrect solutions, we show them to the model.
        print(f"===== Starting iteration {ps_sol_index} =====")
        inv_template_message = {"role": "user", "content": ps_prompt}

        if len(ps_sols) > 0:
            messages_for_new_sol = [
                inv_template_message,
                {"role": "assistant", "content": "\n".join(ps_sols)},
                {"role": "user", "content": TEMPLATE_ERR},
            ]
        else:
            messages_for_new_sol = [inv_template_message]
        ps_sol = get_solution_from_llm(llm_model, messages_for_new_sol)
        ps_sols.append(ps_sol)

        # Check if the solution passes the parser. If it does, we can continue to the next step. Otherwise, we would like to generate another PS.
        lambda_exprs: dict[Expr, str] = {}
        arg_name_to_count: dict[str, int] = {}
        try:
            _, ps_fn_decls, ps_inv_calls = check_solution(
                solution=ps_sol,
                expected_num_funcs=1,
                dsl_code=dsl_code,
                lambda_exprs=lambda_exprs,
                arg_name_to_count=arg_name_to_count,
            )
            print("Passed the parser, continuing to invariant generation")
            print("PS solution", ps_sol)
        except Exception as e:
            print("Failed to pass the parser", e, ps_sol)
            print("Skipping invariant generation")
            continue

        process_synthesized_fn_decls(
            output_var=output_var,
            benchmark_name=fn_name,
            synthesized_fn_decls=ps_fn_decls,
        )

        # If there is no loop_info, this is a loop-free benchmark; skip invariant
        # synthesis and go straight to verification using only the PS function.
        if loop_info is None:
            synthesized_fn_decls = ps_fn_decls
            in_calls = ps_inv_calls

            vc = and_objects(*driver.asserts).src.simplify()
            vc = replace_in_calls(vc, in_calls)
            vc_clauses = [
                replace_in_calls(assert_obj.src, in_calls).simplify()
                for assert_obj in driver.asserts
            ]

            if verification_method == VerificationMethod.SMT:
                verified = verify_benchmark_smt(
                    driver=driver,
                    benchmark_name=fn_name,
                    synthesized_fn_decls=synthesized_fn_decls,
                    in_calls=in_calls,
                    dsl_fns=dsl_fns,
                    vc_clauses=vc_clauses,
                    dsl_fn_name_to_axioms=dsl_fn_name_to_axioms,
                    additional_axioms=additional_axioms,
                )
            elif verification_method == VerificationMethod.ROSETTE:
                verified = verify_benchmark_rosette(
                    driver=driver,
                    benchmark_name=fn_name,
                    synthesized_fn_decls=synthesized_fn_decls,
                    in_calls=in_calls,
                    dsl_fns=dsl_fns,
                    vc=vc,
                    list_bound=list_bound,
                )
            elif verification_method == VerificationMethod.NONE:
                print("Skpping verification...")
                verified = True
            else:
                raise Exception(
                    f"Unsupported verification method {verification_method}"
                )

            if verified:
                print("Solution verified")
                found_sol = True
                final_synthesized_fn_decls = synthesized_fn_decls
                break

            # If PS-only verification failed, continue to the next PS candidate.
            continue

        # Generate the invariant
        print("PS function declarations", ps_fn_decls)
        ps_fn_decl = next(fn_decl for fn_decl in ps_fn_decls if "ps" in fn_decl.name())

        inv_prompt = get_inv_prompt(
            fn_name=fn_name,
            source_code=source_code,
            ps_fn_decl=ps_fn_decl,
            loop_info=loop_info,
            dsl_code=dsl_code,
        )
        inv_sols: list[str] = []
        expected_inv_signatures: list[list[Object]]
        if isinstance(loop_info, SingleLoopInfo):
            expected_inv_signatures = [get_inv_args(loop_info)]  # type: ignore[list-item]
        elif isinstance(loop_info, NestedLoopInfo):
            outer_inv_args, inner_inv_args = get_inv_args(loop_info)  # type: ignore[misc]
            expected_inv_signatures = [outer_inv_args, inner_inv_args]
        else:
            expected_inv_signatures = get_inv_args(loop_info)  # type: ignore[assignment]
        for inv_sol_index in range(max_num_inv_sols):
            print(f"----- Generating {inv_sol_index} invariant -----")
            inv_template_message = {"role": "user", "content": inv_prompt}

            if len(inv_sols) > 0:
                messages_for_new_sol = [
                    inv_template_message,
                    {"role": "assistant", "content": "\n".join(inv_sols)},
                    {"role": "user", "content": TEMPLATE_ERR},
                ]
            else:
                messages_for_new_sol = [inv_template_message]
            inv_sol = get_solution_from_llm(llm_model, messages_for_new_sol)
            if inv_sol is None:
                print("Did not generate invariant solution")
                continue
            print("Generated new INV solution", inv_sol)
            inv_sols.append(inv_sol)

            try:
                expected_num_inv_funcs = (
                    len(loop_info.loop_infos)
                    if isinstance(loop_info, SequentialLoopInfo)
                    else 1
                    if isinstance(loop_info, SingleLoopInfo)
                    else 2
                )
                _, inv_fn_decls, inv_in_calls = check_solution(
                    solution=inv_sol,
                    expected_num_funcs=expected_num_inv_funcs,
                    dsl_code=dsl_code,
                    lambda_exprs=lambda_exprs,
                    arg_name_to_count=arg_name_to_count,
                    expected_signatures=expected_inv_signatures,
                )
                print("Passed the parser, continuing to verification")
            except Exception as e:
                print("Failed to pass the parser", e)
                continue

            process_synthesized_fn_decls(
                output_var=output_var,
                benchmark_name=fn_name,
                synthesized_fn_decls=inv_fn_decls,
                num_invariants=expected_num_inv_funcs,
            )

            synthesized_fn_decls = list(set([*ps_fn_decls, *inv_fn_decls]))
            in_calls = [*ps_inv_calls, *inv_in_calls]

            # This is a hack for dissolve_blend_8
            if fn_name == "dissolve_blend_8":
                # Process synthesized functions.
                for idx, fn_decl in enumerate(synthesized_fn_decls):
                    if "select_two_args_arg" in fn_decl.name():
                        new_args = [
                            *fn_decl.arguments(),
                            Int("opacity").src,
                            Int("rand_cons").src,
                        ]
                        fn_decl.set_arguments(new_args)

                    fn_decl = replace_fn_name(
                        expr=fn_decl,
                        new_fn_name=DISSOLVE_MATRIX_SELECTION_TWO_ARGS,
                        fn_name=MATRIX_SELECTION_TWO_ARGS,
                    )
                    fn_decl = replace_fn_name(
                        expr=fn_decl,
                        new_fn_name=DISSOLVE_SELECTION_TWO_ARGS,
                        fn_name=SELECTION_TWO_ARGS,
                    )
                    fn_decl = augment_arguments(
                        expr=fn_decl,
                        fn_name=DISSOLVE_MATRIX_SELECTION_TWO_ARGS,
                        new_args=[Int("opacity").src, Int("rand_cons").src],
                        start_index=2,
                    )
                    fn_decl = augment_arguments(
                        expr=fn_decl,
                        fn_name=DISSOLVE_SELECTION_TWO_ARGS,
                        new_args=[Int("opacity").src, Int("rand_cons").src],
                        start_index=2,
                    )

                    synthesized_fn_decls[idx] = fn_decl

                # Process in_calls.
                for idx, in_call in enumerate(in_calls):
                    new_in_call: list[str] = []
                    for i in range(len(in_call)):
                        if in_call[i] == MATRIX_SELECTION_TWO_ARGS:
                            new_in_call.append(DISSOLVE_MATRIX_SELECTION_TWO_ARGS)
                        elif in_call[i] == SELECTION_TWO_ARGS:
                            new_in_call.append(DISSOLVE_SELECTION_TWO_ARGS)
                        elif in_call[i] == SELECT_TWO_ARGS_ARG:
                            new_in_call.append(DISSOLVE_SELECT_TWO_ARGS_ARG)
                        else:
                            new_in_call.append(in_call[i])
                    in_calls[idx] = tuple(new_in_call)

                # Process DSL functions.
                for idx, fn_decl in enumerate(dsl_fns):
                    if fn_decl.name() == MATRIX_SELECTION_TWO_ARGS:
                        dsl_fns[idx] = dissolve_matrix_selection_two_args_fn_decl
                    elif fn_decl.name() == SELECTION_TWO_ARGS:
                        dsl_fns[idx] = dissolve_selection_two_args_fn_decl

            # Generate VC.
            # Write assertions
            vc = and_objects(*driver.asserts).src.simplify()
            vc = replace_in_calls(vc, in_calls)
            vc_clauses = [
                replace_in_calls(assert_obj.src, in_calls).simplify()
                for assert_obj in driver.asserts
            ]

            # Verify the solution
            if verification_method == VerificationMethod.SMT:
                verified = verify_benchmark_smt(
                    driver=driver,
                    benchmark_name=fn_name,
                    synthesized_fn_decls=synthesized_fn_decls,
                    in_calls=in_calls,
                    dsl_fns=dsl_fns,
                    vc_clauses=vc_clauses,
                    dsl_fn_name_to_axioms=dsl_fn_name_to_axioms,
                    additional_axioms=additional_axioms,
                )
            elif verification_method == VerificationMethod.ROSETTE:
                verified = verify_benchmark_rosette(
                    driver=driver,
                    benchmark_name=fn_name,
                    synthesized_fn_decls=synthesized_fn_decls,
                    in_calls=in_calls,
                    dsl_fns=dsl_fns,
                    vc=vc,
                    list_bound=list_bound,
                )
            elif verification_method == VerificationMethod.NONE:
                print("Skpping verification...")
            else:
                raise Exception(
                    f"Unsupported verification method {verification_method}"
                )

            if verified:
                print("Solution verified")
                found_sol = True
                final_synthesized_fn_decls = synthesized_fn_decls
                break

        # If we have a correct solution, we can break out of the loop.
        if found_sol:
            break

    if not found_sol:
        raise Exception("No correct solution found")
    if final_synthesized_fn_decls is None:
        raise Exception("No synthesized function declarations captured")

    print("Found PS solution")
    print(ps_sol)
    return final_synthesized_fn_decls


def run_synthesis_for_cc(
    cc_path: str,
    fn_name: str,
    *,
    precondition_fn: Optional[Callable[[Driver, dict], None]] = None,
    llm_model: Optional[LLMModel] = None,
    verification_method: Optional[VerificationMethod] = None,
    dsl_fns: Optional[list[FnDecl | FnDeclRecursive]] = None,
    dsl_fn_name_to_axioms: Optional[dict[str, list[Axiom]]] = None,
    additional_axioms: Optional[list[Axiom]] = None,
    list_bound: int = 2,
) -> list[FnDecl | FnDeclRecursive]:
    """
    Run LLM-guided synthesis for a single-function .cc file.

    Infers loop info from the compiled LLVM, builds input/output variables from
    the source AST, and runs the synthesis algorithm. The .cc file is expected
    to compile to .ll and .loops (via the standard compile-add-blocks pipeline).

    Intended for use by driver scripts under tenspiler/*/llm/driver/ and similar.

    Args:
        cc_path: Path to the C++ source file (e.g. "tenspiler/llama/cpp/for_synthesis/softmax/softmax_part1.cc").
        fn_name: Name of the function to synthesize (e.g. "softmax_part1").
        precondition_fn: Optional callback (driver, input_vars) to add preconditions
            (e.g. bounds on inputs) before running the VC.
        llm_model: LLM to use for synthesis (default: LLMModel.GPT).
        verification_method: SMT or Rosette (default: VerificationMethod.ROSETTE).
        dsl_fns: DSL function declarations (default: TENSPILER_FNS).
        dsl_fn_name_to_axioms: Axioms per DSL fn (default: {}).
        additional_axioms: Additional axioms to add to the synthesis (default: None).
        list_bound: List bound for the synthesis (default: 2).
    """
    if dsl_fns is None:
        dsl_fns = TENSPILER_FNS
    if dsl_fn_name_to_axioms is None:
        dsl_fn_name_to_axioms = {}
    if additional_axioms is None:
        additional_axioms = []
    if llm_model is None:
        llm_model = LLMModel.GPT
    if verification_method is None:
        verification_method = VerificationMethod.ROSETTE

    subprocess.run(
        ["metalift/utils/llvm/compile-add-blocks", cc_path],
        check=True,
    )

    driver = Driver()

    # Infer loop structure from LLVM (.ll + .loops). If no loops are present,
    # we synthesize only the postcondition (no invariants).
    # Loop info is none when there are no loops in the function.
    loop_info: SingleLoopInfo | NestedLoopInfo | SequentialLoopInfo | None = None
    root_node = find_root_node_from_file(cc_path)
    num_loops = get_num_loops(root_node)
    if num_loops == 1:
        loop_info = infer_single_loop_info_from_llvm(
            driver=driver,
            cc_path=cc_path,
            fn_name=fn_name,
        )
    elif has_nested_loops(root_node):
        if num_loops != 2:
            raise ValueError(
                f"Nested-loop mode currently expects 2 loops, got {num_loops}"
            )
        loop_info = infer_nested_loop_info_from_llvm(
            driver=driver,
            cc_path=cc_path,
            fn_name=fn_name,
        )
    elif num_loops > 1:
        loop_info = infer_sequential_loop_info_from_llvm(
            driver=driver,
            cc_path=cc_path,
            fn_name=fn_name,
        )

    # Build input variables from the source tree (ordered as in the function signature).
    root_node = find_root_node_from_file(cc_path)
    input_vars = make_input_variables(root_node, driver, fn_name)
    input_var_list = list(input_vars.values())

    # Optional: let the caller add preconditions (e.g. input_var.len() > 0).
    if precondition_fn is not None:
        precondition_fn(driver, input_vars)

    if loop_info is None:
        inv_grammars = {}
    else:
        inv_args = get_inv_args(loop_info)
        if isinstance(loop_info, NestedLoopInfo):
            inv_grammars = {
                f"{fn_name}_inv0": InvGrammar(None, [], inv_args[0]),
                f"{fn_name}_inv1": InvGrammar(None, [], inv_args[1]),
            }
        elif isinstance(loop_info, SequentialLoopInfo):
            inv_grammars = {
                f"{fn_name}_inv{i}": InvGrammar(None, [], args)
                for i, args in enumerate(inv_args)
            }
        else:
            inv_grammars = {f"{fn_name}_inv0": InvGrammar(None, [], inv_args)}

    # Analyze the function and build the VC (asserts) used for verification.
    mf = driver.analyze(
        llvm_filepath=cc_path.replace(".cc", ".ll"),
        loops_filepath=cc_path.replace(".cc", ".loops"),
        fn_name=fn_name,
        target_lang_fn=[],
        inv_grammars=inv_grammars,
        ps_grammar=None,
    )
    mf(*input_var_list)

    # Rebuild loop_info with types from var_tracker (after VC) so prompts see refined types.
    if loop_info is not None:
        loop_info = prepare_loop_info_from_driver(loop_info, driver)

    # Infer output variable from return statement and function return type.
    return_name = get_return_var_name(root_node, fn_name)
    if return_name is None:
        raise ValueError(
            "Could not infer return variable from source (expected simple 'return id;')"
        )
    var_map = {var.name(): var for var in driver.var_tracker.all()}
    return_name = f"{fn_name}_rv"
    output_var = create_object(var_map[return_name].type, return_name)

    source_code = Path(cc_path).read_text()

    return run_llm_synthesis_algorithm(
        driver=driver,
        loop_info=loop_info,
        output_var=output_var,
        source_code=source_code,
        fn_name=fn_name,
        llm_model=llm_model,
        dsl_fns=dsl_fns,
        dsl_fn_name_to_axioms=dsl_fn_name_to_axioms,
        additional_axioms=additional_axioms,
        verification_method=verification_method,
        list_bound=list_bound,
    )


def get_solution_from_claude(messages: list[dict[str, Any]]) -> str:
    print("running with claude")
    api_key = os.getenv("CLAUDE_API_KEY")
    if not api_key:
        raise RuntimeError(
            "CLAUDE_API_KEY is not set but LLMModel.CLAUDE was requested"
        )
    claude_client = anthropic.Anthropic(api_key=api_key)
    message = claude_client.messages.create(
        model="claude-3-5-sonnet-20240620",
        max_tokens=1000,
        temperature=0.7,
        system=TEMPLATE_SYS,
        messages=messages,
    )
    raw_solutions = extract_all_python_functions(message.content[0].text)
    return [replace_ite(raw_solution) for raw_solution in raw_solutions]


def get_solution_from_gpt(messages: list[dict[str, Any]]) -> str:
    print("running with gpt")
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        raise RuntimeError("OPENAI_API_KEY is not set but LLMModel.GPT was requested")
    openai_client = OpenAI(api_key=api_key)
    messages_with_sys = [{"role": "system", "content": TEMPLATE_SYS}, *messages]
    outputs = openai_client.chat.completions.create(
        model="gpt-5.4",
        messages=messages_with_sys,
        n=1,
        temperature=0.7,
    )
    outputs = [choice.message.content for choice in outputs.choices]
    raw_output = "\n\n".join(extract_all_python_functions(outputs[0]))
    extracted_output = replace_ite(raw_output)
    return extracted_output


def get_solution_from_gemini(messages: list[dict[str, Any]]) -> str:
    print("running with gemini")
    messages_copy = copy.deepcopy(messages)
    for message in messages_copy:
        if message["role"] == "assistant":
            message["role"] = "model"
        message["parts"] = message["content"]
        del message["content"]

    generation_config = {
        "temperature": 0.7,
        "top_p": 0.95,
        "top_k": 64,
        "max_output_tokens": 8192,
        "response_mime_type": "text/plain",
    }

    model = genai.GenerativeModel(
        model_name="gemini-1.5-pro-exp-0827",  # "gemini-1.5-pro-exp-0827",
        generation_config=generation_config,
    )

    chat_session = model.start_chat(history=messages_copy[:-1])
    response = chat_session.send_message(messages_copy[-1]["parts"])
    raw_solution = extract_all_python_functions(response.text)[0]
    extracted_solution = replace_ite(raw_solution)
    return extracted_solution


def get_solution_from_bedrock(messages: list[dict[str, Any]]) -> str | None:
    print("running with bedrock")
    bedrock_client = boto3.client(
        "bedrock-runtime",
        region_name=os.getenv("AWS_REGION", "us-east-1"),
    )
    bedrock_messages = []
    for msg in messages:
        bedrock_messages.append(
            {
                "role": msg["role"],
                "content": [{"text": msg["content"]}],
            }
        )

    response = bedrock_client.converse(
        modelId=BEDROCK_MODEL_ID,
        system=[{"text": TEMPLATE_SYS}],
        messages=bedrock_messages,
        inferenceConfig={
            # "maxTokens": 1024,
            "temperature": 0.0,
            "topP": 0.9,
        },
    )

    output_text = "".join(
        block["text"]
        for block in response["output"]["message"]["content"]
        if "text" in block
    )
    raw_solution = extract_all_python_functions(output_text)
    if raw_solution:
        return replace_ite(raw_solution[0])
    else:
        return None


def get_solution_from_llm(
    llm_model: LLMModel, messages: list[dict[str, Any]]
) -> str | None:
    if llm_model == LLMModel.CLAUDE:
        return get_solution_from_claude(messages)
    elif llm_model == LLMModel.GPT:
        return get_solution_from_gpt(messages)
    elif llm_model == LLMModel.GEMINI:
        return get_solution_from_gemini(messages)
    elif llm_model == LLMModel.BEDROCK:
        return get_solution_from_bedrock(messages)
    raise ValueError(f"Invalid LLM model {llm_model}")
