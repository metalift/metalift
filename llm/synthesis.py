import copy
import os
import subprocess
from enum import Enum
from pathlib import Path
from typing import Any, Union

import google.generativeai as genai

from llm.constants import (
    CLAUDE_CLIENT,
    OPENAI_CLIENT,
    SYNTHESIS_LOGS_DIR,
    TEMPLATE_ERR,
    TEMPLATE_SYS,
)
from llm.parser import check_solution
from llm.prompts import get_inv_prompt, get_ps_prompt
from llm.utils import (
    DoubleLoopInfo,
    SingleLoopInfo,
    extract_all_python_functions,
    replace_ite,
)
from metalift.frontend.llvm import Driver
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
    is_fn_decl_type,
)
from metalift.rosette_translator import generate_vars
from metalift.smt_util import augment_arguments, replace_fn_name, toSMT
from metalift.synthesis_common import get_used_fn_names
from metalift.vc_util import and_objects
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


class VerificationMethod(Enum):
    NONE = "none"
    ROSETTE = "rosette"
    SMT = "smt"


class LLMModel(Enum):
    CLAUDE = "claude"
    GPT = "gpt"
    GEMINI = "gemini"


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


def run_llm_synthesis_algorithm(
    *,
    driver: Driver,
    loop_info: SingleLoopInfo | DoubleLoopInfo,
    output_var: Object,
    source_code: str,
    benchmark_name: str,
    llm_model: LLMModel,
    dsl_fns: list[FnDecl | FnDeclRecursive],
    dsl_fn_name_to_axioms: dict[str, list[Axiom]],
    max_num_ps_sols: int = 10,
    max_num_inv_sols: int = 10,
    verification_method: VerificationMethod = VerificationMethod.SMT,
) -> None:
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
    ps_prompt = get_ps_prompt(dsl_code=dsl_code, source_code=source_code)

    # Get result from LLM
    ps_sols: list[str] = []
    found_sol = False
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
        except Exception as e:
            print("Failed to pass the parser", e)
            print("Skipping invariant generation")
            continue

        process_synthesized_fn_decls(
            output_var=output_var,
            benchmark_name=benchmark_name,
            synthesized_fn_decls=ps_fn_decls,
        )

        # Generate the invariant
        ps_fn_decl = next(fn_decl for fn_decl in ps_fn_decls if "ps" in fn_decl.name())
        inv_prompt = get_inv_prompt(
            source_code=source_code,
            ps_fn_decl=ps_fn_decl,
            loop_info=loop_info,
            dsl_code=dsl_code,
        )
        inv_sols: list[str] = []
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
            print("Generated new INV solution", inv_sol)
            inv_sols.append(inv_sol)

            try:
                _, inv_fn_decls, inv_in_calls = check_solution(
                    solution=inv_sol,
                    expected_num_funcs=1
                    if isinstance(loop_info, SingleLoopInfo)
                    else 2,
                    dsl_code=dsl_code,
                    lambda_exprs=lambda_exprs,
                    arg_name_to_count=arg_name_to_count,
                )
                print("Passed the parser, continuing to verification")
            except Exception as e:
                print("Failed to pass the parser", e)
                continue

            process_synthesized_fn_decls(
                output_var=output_var,
                benchmark_name=benchmark_name,
                synthesized_fn_decls=inv_fn_decls,
            )

            synthesized_fn_decls = list(set([*ps_fn_decls, *inv_fn_decls]))
            in_calls = [*ps_inv_calls, *inv_in_calls]

            # This is a hack for dissolve_blend_8
            if benchmark_name == "dissolve_blend_8":
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

            # Verify the solution
            if verification_method == VerificationMethod.SMT:
                verified = verify_benchmark_smt(
                    driver=driver,
                    benchmark_name=benchmark_name,
                    synthesized_fn_decls=synthesized_fn_decls,
                    in_calls=in_calls,
                    dsl_fns=dsl_fns,
                    vc=vc,
                    dsl_fn_name_to_axioms=dsl_fn_name_to_axioms,
                )
            elif verification_method == VerificationMethod.ROSETTE:
                verified = verify_benchmark_rosette(
                    driver=driver,
                    benchmark_name=benchmark_name,
                    synthesized_fn_decls=synthesized_fn_decls,
                    in_calls=in_calls,
                    dsl_fns=dsl_fns,
                    vc=vc,
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
                break

        # If we have a correct solution, we can break out of the loop.
        if found_sol:
            break

    if not found_sol:
        raise Exception("No correct solution found")

    print("Found PS solution")
    print(ps_sol)


def get_solution_from_claude(messages: list[dict[str, Any]]) -> str:
    print("running with claude")
    message = CLAUDE_CLIENT.messages.create(
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
    messages_with_sys = [{"role": "system", "content": TEMPLATE_SYS}, *messages]
    outputs = OPENAI_CLIENT.chat.completions.create(
        model="gpt-4o",
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


def get_solution_from_llm(llm_model: LLMModel, messages: list[dict[str, Any]]) -> str:
    if llm_model == LLMModel.CLAUDE:
        return get_solution_from_claude(messages)
    elif llm_model == LLMModel.GPT:
        return get_solution_from_gpt(messages)
    elif llm_model == LLMModel.GEMINI:
        return get_solution_from_gemini(messages)
    raise ValueError(f"Invalid LLM model {llm_model}")
