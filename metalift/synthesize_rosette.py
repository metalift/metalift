import os
import subprocess
import time
import typing
from importlib import resources
from pathlib import Path
from typing import Any, Callable, Dict, List, Union

import pyparsing as pp

from metalift import process_tracker, utils
from metalift.analysis import CodeInfo
from metalift.exceptions import CVC5UnsupportedException
from metalift.ir import (
    Add,
    And,
    Axiom,
    Bool,
    BoolLit,
    Call,
    Div,
    Eq,
    Expr,
    Fn,
    FnDecl,
    FnDeclRecursive,
    Ge,
    Gt,
    Implies,
    Int,
    IntLit,
    Ite,
    Le,
    Let,
)
from metalift.ir import List as mlList
from metalift.ir import Lit, Lt, Matrix, Mod, Mul, Not, ObjectT, Or
from metalift.ir import Set as mlSet
from metalift.ir import (
    Sub,
    Synth,
    Target,
    TupleExpr,
    TupleGet,
    Var,
    get_fn_return_type,
    get_list_element_type,
)
from metalift.rosette_translator import to_rosette
from metalift.synthesis_common import (
    SynthesisFailed,
    VerificationFailed,
    generate_types,
    prune_fn_decls,
    verify_synth_result,
)
from tests.python.utils.utils import codegen


# utils for converting rosette output to IR
# TODO: mypy 0.95 says parseString returns Any instead of ParseResults despite what pyparse's doc says
def generate_ast(expr: str) -> Union[Any, pp.ParseResults]:
    s_expr = pp.nestedExpr(opener="(", closer=")")
    parser = pp.ZeroOrMore(s_expr)
    try:
        ast = parser.parseString(expr, parseAll=True).asList()
    except:
        raise Exception(f"Failed to parse Rosette output: {expr}")
    return ast


def parse_output(resultSynth: typing.List[str]) -> typing.List[str]:
    output = []
    for i in range(len(resultSynth)):
        s = ""
        if "define" in resultSynth[i]:
            s = resultSynth[i]
            for j in range(i + 1, len(resultSynth)):
                if "/" not in resultSynth[j]:
                    s += resultSynth[j]
                else:
                    i = j + 1
                    break
            output.append(s)
    return output


def convert_expr(expr: Any) -> Expr:
    if isinstance(expr, Call) and expr.name() == "list_eq":
        return Eq(expr.arguments()[0], expr.arguments()[1])
    return expr


def to_expr(
    ast: typing.List[Any],
    fnsType: Dict[Any, Any],
    varType: Dict[str, ObjectT],
    choices: Dict[str, Expr],
    typeHint: typing.Optional[ObjectT] = None,
) -> Expr:
    expr_bi: Dict[str, Callable[..., Expr]] = {
        "equal?": Eq,
        "+": Add,
        "-": Sub,
        "*": Mul,
        "quotient-noerr": Div,
        "<": Lt,
        "<=": Le,
        ">": Gt,
        ">=": Ge,
        "&&": And,
        "or": Or,
        "=>": Implies,
        "remainder": Mod,
    }
    expr_uni = {"!": Not}
    if isinstance(ast, list):
        if ast[0] == "define":
            return to_expr(ast[2], fnsType, varType, choices)
        elif ast[0] == "choose":
            # TODO: now that we have chooseArbitrarily we could parse things properly
            return to_expr(ast[1], fnsType, varType, choices)
        elif ast[0] in expr_bi.keys():
            return expr_bi[ast[0]](
                *[
                    to_expr(ast[i], fnsType, varType, choices)
                    for i in range(1, len(ast))
                ]
            )
        elif ast[0] in expr_uni.keys():
            return expr_uni[ast[0]](to_expr(ast[1], fnsType, varType, choices))
        elif ast[0] == "if":
            v1 = to_expr(ast[2], fnsType, varType, choices)
            v2 = to_expr(ast[3], fnsType, varType, choices)

            if v1.type == None:
                v1.type = v2.type
            if v2.type == None:
                v2.type = v1.type

            return Ite(
                to_expr(ast[1], fnsType, varType, choices),
                v1,
                v2,
            )
        elif ast[0] == "=":
            return Eq(
                to_expr(ast[1], fnsType, varType, choices),
                to_expr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "length":
            return Call("list_length", Int, to_expr(ast[1], fnsType, varType, choices))
        elif ast[0] == "matrix-length":
            return Call(
                "matrix_length", Int, to_expr(ast[1], fnsType, varType, choices)
            )
        elif ast[0] == "tensor3d-length":
            return Call(
                "tensor3d_length", Int, to_expr(ast[1], fnsType, varType, choices)
            )
        elif ast[0] == "list-empty":
            return Call("list_empty", mlList[Int])
        elif ast[0] == "matrix-empty":
            return Call("matrix_empty", mlList[mlList[Int]])
        elif ast[0] == "tensor3d-empty":
            return Call("tensor3d_empty", mlList[mlList[mlList[Int]]])
        elif ast[0] == "list-append":
            list_expr = to_expr(ast[1], fnsType, varType, choices)
            elem = to_expr(ast[2], fnsType, varType, choices)
            return Call(
                "list_append",
                list_expr.type,
                list_expr,
                elem,
            )
        elif ast[0] == "matrix-append":
            list_expr = to_expr(ast[1], fnsType, varType, choices)
            elem = to_expr(ast[2], fnsType, varType, choices)
            return Call(
                "matrix_append",
                list_expr.type,
                list_expr,
                elem,
            )
        elif ast[0] == "tensor3d-append":
            tensor_expr = to_expr(ast[1], fnsType, varType, choices)
            elem = to_expr(ast[2], fnsType, varType, choices)
            return Call(
                "tensor3d_append",
                tensor_expr.type,
                tensor_expr,
                elem,
            )
        elif ast[0] == "list-prepend":
            elem = to_expr(ast[1], fnsType, varType, choices)
            lst = to_expr(ast[2], fnsType, varType, choices)
            return Call(
                "list_prepend",
                lst.type,
                elem,
                lst,
            )
        elif ast[0] == "matrix-prepend":
            elem = to_expr(ast[1], fnsType, varType, choices)
            lst = to_expr(ast[2], fnsType, varType, choices)
            return Call(
                "matrix_prepend",
                lst.type,
                elem,
                lst,
            )
        elif ast[0] == "tensor3d-prepend":
            elem = to_expr(ast[1], fnsType, varType, choices)
            tensor = to_expr(ast[2], fnsType, varType, choices)
            return Call(
                "tensor3d_prepend",
                tensor.type,
                elem,
                tensor,
            )
        elif ast[0] == "list-ref-noerr":
            list_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "list_get",
                get_list_element_type(list_expr.type),
                list_expr,
                to_expr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "matrix-ref-noerr":
            list_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "matrix_get",
                get_list_element_type(list_expr.type),
                list_expr,
                to_expr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "tensor3d-ref-noerr":
            tensor_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "tensor3d_get",
                Matrix[
                    Int
                ],  # TODO for now we can assume this is matrix[int] since we only support int lists
                tensor_expr,
                to_expr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "list-tail-noerr":
            list_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "list_tail",
                list_expr.type,
                list_expr,
                to_expr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "matrix-tail-noerr":
            list_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "matrix_tail",
                list_expr.type,
                list_expr,
                to_expr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "tensor3d-tail-noerr":
            tensor_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "tensor3d_tail",
                tensor_expr.type,
                tensor_expr,
                to_expr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "list-concat":
            lst1 = to_expr(ast[1], fnsType, varType, choices)
            lst2 = to_expr(ast[2], fnsType, varType, choices)
            return Call("list_concat", lst1.type, lst1, lst2)
        elif ast[0] == "list-take-noerr":
            list_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "list_take",
                list_expr.type,
                list_expr,
                to_expr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "matrix-take-noerr":
            list_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "matrix_take",
                list_expr.type,
                list_expr,
                to_expr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "tensor3d-take-noerr":
            tensor_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "tensor3d_take",
                tensor_expr.type,
                tensor_expr,
                to_expr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "vec-slice-noerr":
            list_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "vec_slice",
                list_expr.type,
                list_expr,
                to_expr(ast[2], fnsType, varType, choices),
                to_expr(ast[3], fnsType, varType, choices),
            )
        elif ast[0] == "matrix-row-slice-noerr":
            list_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "matrix_row_slice",
                list_expr.type,
                list_expr,
                to_expr(ast[2], fnsType, varType, choices),
                to_expr(ast[3], fnsType, varType, choices),
            )
        elif ast[0] == "vec-slice-with-length-noerr":
            list_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "vec_slice_with_length",
                list_expr.type,
                list_expr,
                to_expr(ast[2], fnsType, varType, choices),
                to_expr(ast[3], fnsType, varType, choices),
            )
        elif ast[0] == "matrix-row-slice-with-length-noerr":
            list_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "matrix_row_slice_with_length",
                list_expr.type,
                list_expr,
                to_expr(ast[2], fnsType, varType, choices),
                to_expr(ast[3], fnsType, varType, choices),
            )
        elif ast[0] == "matrix-col-slice-noerr":
            list_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "matrix_col_slice",
                list_expr.type,
                list_expr,
                to_expr(ast[2], fnsType, varType, choices),
                to_expr(ast[3], fnsType, varType, choices),
            )
        elif ast[0] == "matrix-col-slice-with-length-noerr":
            list_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call(
                "matrix_col_slice_with_length",
                list_expr.type,
                list_expr,
                to_expr(ast[2], fnsType, varType, choices),
                to_expr(ast[3], fnsType, varType, choices),
            )
        elif ast[0] == "matrix-transpose-noerr":
            matrix_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call("matrix_transpose", matrix_expr.type, matrix_expr)
        elif ast[0] == "integer-sqrt-noerr":
            int_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call("integer_sqrt", Int, int_expr)
        elif ast[0] == "integer-exp-noerr":
            int_expr = to_expr(ast[1], fnsType, varType, choices)
            return Call("integer_exp", Int, int_expr)
        elif ast[0] == "make-tuple":
            arg_eval = []
            for alen in range(1, len(ast)):
                arg_eval.append(to_expr(ast[alen], fnsType, varType, choices))
            return TupleExpr(*arg_eval)
        elif ast[0] == "tupleGet":
            return TupleGet(
                to_expr(ast[1], fnsType, varType, choices),
                to_expr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "set-create":
            return Call(ast[0], mlSet[Int])
        elif ast[0] == "set-insert":
            v = to_expr(ast[1], fnsType, varType, choices)
            s1 = to_expr(ast[2], fnsType, varType, choices)
            return Call(ast[0], mlSet[v.type], v, s1)  # type: ignore
        elif ast[0] == "set-singleton":
            v = to_expr(ast[1], fnsType, varType, choices)
            return Call(ast[0], mlSet[v.type], v)  # type: ignore
        elif ast[0] == "set-eq":
            s1 = to_expr(ast[1], fnsType, varType, choices)
            s2 = to_expr(ast[2], fnsType, varType, choices)
            return Eq(s1, s2)
        elif ast[0] == "set-union" or ast[0] == "set-minus":
            s1 = to_expr(ast[1], fnsType, varType, choices)
            s2 = to_expr(ast[2], fnsType, varType, choices)
            return Call(ast[0], s1.type, s1, s2)
        elif ast[0] == "set-subset":
            s1 = to_expr(ast[1], fnsType, varType, choices)
            s2 = to_expr(ast[2], fnsType, varType, choices)
            return Call(ast[0], Bool, s1, s2)
        elif ast[0] == "set-member":
            v = to_expr(ast[1], fnsType, varType, choices)
            s = to_expr(ast[2], fnsType, varType, choices)
            return Call(ast[0], Bool, v, s)
        elif ast[0] == "map-union":
            m1 = to_expr(ast[1], fnsType, varType, choices)
            m2 = to_expr(ast[2], fnsType, varType, choices)

            if m1.type == None:
                m1.type = m2.type
            if m2.type == None:
                m2.type = m1.type

            uf = to_expr(
                ast[3],
                fnsType,
                varType,
                choices,
                typeHint=FnT(m1.type.args[1], m1.type.args[1], m1.type.args[1]),  # type: ignore
            )

            return Call(ast[0], m1.type, m1, m2, uf)
        elif ast[0] == "map-values":
            m = to_expr(ast[1], fnsType, varType, choices)
            return Call(ast[0], mlList[m.type.args[1]], m)  # type: ignore
        elif ast[0] == "map-singleton":
            k = to_expr(ast[1], fnsType, varType, choices)
            v = to_expr(ast[2], fnsType, varType, choices)
            return Call(ast[0], MapT(k.type, v.type), k, v)  # type: ignore
        elif ast[0] == "map-create":
            return Call(ast[0], MapT(None, None))  # type: ignore
        elif ast[0] == "map-get":
            m = to_expr(ast[1], fnsType, varType, choices)
            k = to_expr(ast[2], fnsType, varType, choices)
            default = to_expr(ast[3], fnsType, varType, choices)
            return Call(ast[0], m.type.args[1], m, k, default)  # type: ignore
        elif ast[0] == "lambda":
            arg_list = [
                Var(n, t) for (t, n) in zip(typeHint.args[1:], ast[1])  # type: ignore
            ]

            varTypeUpdated = dict(varType)
            for a in arg_list:
                varTypeUpdated[a.args[0]] = a.type

            body = to_expr(ast[2], fnsType, varTypeUpdated, choices)
            return Lambda(body.type, body, *arg_list)  # type: ignore
        elif ast[0] == "let":
            var_value = to_expr(ast[1][0][1], fnsType, varType, choices)
            tmp_var_type = dict(varType)
            tmp_var_type[ast[1][0][0]] = var_value.type
            return Let(
                Var(ast[1][0][0], var_value.type),
                var_value,
                to_expr(ast[2], fnsType, tmp_var_type, choices),
            )
        elif ast[0] == "reduce_int":
            data = to_expr(ast[1], fnsType, varType, choices)
            fn = to_expr(
                ast[2],
                fnsType,
                varType,
                choices,
                typeHint=FnT(Int, data.type.args[0], Int),  # type: ignore
            )
            initial = to_expr(ast[3], fnsType, varType, choices)
            return Call("reduce_int", Int, data, fn, initial)
        elif ast[0] == "reduce_bool":
            data = to_expr(ast[1], fnsType, varType, choices)
            fn = to_expr(
                ast[2],
                fnsType,
                varType,
                choices,
                typeHint=FnT(Bool, data.type.args[0], Bool),  # type: ignore
            )
            initial = to_expr(ast[3], fnsType, varType, choices)
            return Call("reduce_bool", Bool, data, fn, initial)
        elif ast[0] in fnsType.keys():
            arg_eval = []
            ret_type = get_fn_return_type(fnsType[ast[0]])
            for alen in range(1, len(ast)):
                arg_eval.append(
                    to_expr(
                        ast[alen],
                        fnsType,
                        varType,
                        choices,
                        typeHint=ret_type,
                    )
                )
            if (
                ast[0] in Target.definedFns
            ):  # re-create a Target obj to call the user provided codegen
                return Target.definedFns[ast[0]].call(*arg_eval)
            else:
                return Call(ast[0], ret_type, *arg_eval)
        elif ast[0] in choices:

            def replace_choices(expr: Expr) -> Expr:
                if (not isinstance(expr, Expr)) or isinstance(expr, Lit):
                    return expr

                if isinstance(expr, Var):
                    if expr.name().startswith("(") and expr.name()[1:-1] in choices:
                        return choices[expr.name()[1:-1]].args[0]
                    return expr
                return expr.map_args(replace_choices)

            picked: Expr = choices[ast[0]].args[0]
            while (
                # picked.kind == Expr.Kind.Var
                isinstance(picked, Var)
                and picked.args[0].startswith("(")
                and picked.args[0][1:-1] in choices
            ):
                picked = choices[picked.args[0][1:-1]].args[0]
            return picked.map_args(replace_choices)
        else:
            raise Exception(f"Unexpected function name: {ast[0]}")
    else:
        if ast.isnumeric():
            return IntLit(int(ast))
        elif ast[0] == "-" and ast[1:].isnumeric():
            return IntLit(-int(ast[1:]))
        elif ast == "true":
            return BoolLit(True)
        elif ast == "false":
            return BoolLit(False)
        elif ast in fnsType.keys():
            return Var(ast, fnsType[ast])
        else:
            return Var(ast, varType[ast])


def to_synthesize(
    loopAndPsInfo: typing.Sequence[Union[CodeInfo, Expr]],
    lang: typing.Sequence[Union[FnDeclRecursive, FnDecl, Axiom]],
) -> typing.List[str]:
    synthNames = []
    for i in loopAndPsInfo:
        if isinstance(i, CodeInfo):
            synthNames.append(i.name)
        else:
            synthNames.append(i.args[0])
    for l in lang:
        if l.args[1] is None:
            synthNames.append(l.args[0])
    return synthNames


def synthesize(
    basename: str,
    target_lang: typing.Sequence[Union[FnDeclRecursive, FnDecl, Axiom]],
    vars: typing.Set[Var],
    inv_and_ps: typing.List[Synth],
    preds: typing.List[Expr],
    vc: Expr,
    loop_and_ps_info: typing.Sequence[Union[CodeInfo, Expr]],
    cvc_path: str,
    uid: int = 1,
    no_verify: bool = False,
    unbounded_ints: bool = False,
    optimize_vc_equality: bool = False,
    list_bound: int = 4,
    log: bool = True,
    uninterp_fns: List[str] = [],
    rounds_to_guess: int = 0,
    fns_to_guess: List[FnDeclRecursive] = [],
    fn_defs_to_exclude: List[FnDeclRecursive] = [],
) -> typing.List[FnDeclRecursive]:
    synth_dir = "./synthesisLogs/"
    if not os.path.exists(synth_dir):
        os.mkdir(synth_dir)
    # synthFile = synthDir + basename + f"_{uid}" + ".rkt"
    synth_file = synth_dir + basename + ".rkt"

    with open(synth_dir + "utils.rkt", "w") as out:
        out.write(resources.read_text(utils, "utils.rkt"))
    with open(synth_dir + "bounded.rkt", "w") as out:
        out.write(resources.read_text(utils, "bounded.rkt"))

    if optimize_vc_equality:
        prev_vc = vc.toSMT()
        new_vars: typing.Set[Var] = set()
        while True:
            expr_count: Dict[str, int] = {}

            vc.src.count_variable_uses(expr_count)  # type: ignore

            vc = vc.src.optimize_useless_equality(expr_count, new_vars)  # type: ignore

            if vc.toSMT() == prev_vc:
                break  # run to fixpoint
            else:
                prev_vc = vc.toSMT()

        vars = vars.union(new_vars)
        for var in list(vars):
            if var.args[0] not in expr_count:
                vars.remove(var)
    else:
        vc = vc.simplify()

    ##### synthesis procedure #####
    choices: Dict[str, Dict[str, Expr]] = {}
    to_rosette(
        basename=basename,
        filename=synth_file,
        target_lang=target_lang,
        vars=vars,
        inv_and_ps=inv_and_ps,
        preds=preds,
        vc=vc,
        loop_and_ps_info=loop_and_ps_info,
        rounds_to_guess=rounds_to_guess,
        fns_to_guess=fns_to_guess,
        fn_defs_to_exclude=fn_defs_to_exclude,
        unbounded_ints=unbounded_ints,
        list_bound=list_bound,
        write_choices_to=choices,
        uninterp_fns=uninterp_fns,
    )

    synth_names = to_synthesize(loop_and_ps_info, target_lang)

    last_processed_sol_idx = -1

    # before we start synthesis, we need to delete all previous solutions.
    for sol_file in Path(synth_dir).glob(f"{basename}_sol*"):
        sol_file.unlink()
    proc_synthesis = subprocess.Popen(
        ["racket", synth_file],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    process_tracker.all_processes.append(proc_synthesis)
    # both last_processed_sol_idx and rounds_to_guess are 0-indexed
    while (
        exit_code := proc_synthesis.poll()
    ) is None or last_processed_sol_idx + 1 < rounds_to_guess + 1:
        time.sleep(2)

        curr_sol_idx = last_processed_sol_idx + 1
        curr_sol_file = Path(f"{synth_dir}/{basename}_sol{curr_sol_idx}")
        curr_sol_exists = curr_sol_file.is_file()
        if not curr_sol_exists:
            continue

        with open(curr_sol_file, "r") as f:
            result_synth = f.read().split("\n")

        ##### End of Synthesis #####

        #####parsing output of rosette synthesis#####
        var_types = {}
        for i in [*loop_and_ps_info, *inv_and_ps]:
            if isinstance(i, CodeInfo):
                var_types[i.name] = generate_types(
                    i.modified_vars + i.read_vars + list(vars)
                )
            else:
                var_types[i.args[0]] = generate_types(i.args[2:])
        for l_i in target_lang:
            var_types[l_i.args[0]] = generate_types(l_i.args[2:])

        if result_synth[0] == "#t":
            output = parse_output(result_synth[1:])
            candidate_dict = {}
            fnsType = generate_types(target_lang)
            for synth_fun in inv_and_ps:
                all_vars = synth_fun.args[2:]
                ce_name = synth_fun.args[0]
                fn_types = (synth_fun.args[1].type, *[v.type for v in all_vars])
                fnsType[ce_name] = Fn[tuple[fn_types]]  # type: ignore
            for n in synth_names:
                for r in output:
                    if "define (" + n + " " in r or "define (" + n + ")" in r:
                        start_index = r.find("(")
                        candidate_dict[n] = to_expr(
                            generate_ast(r[start_index:])[0],
                            fnsType,
                            var_types[n],
                            choices[n] if n in choices else {},
                        )
        else:
            raise SynthesisFailed("Synthesis failed")
        #####candidateDict --> definitions of all functions to be synthesized#####

        ##### generating function definitions of all the functions to be synthesized#####
        candidates_smt: List[FnDeclRecursive] = []
        for synth_fun in inv_and_ps:
            all_vars = synth_fun.args[2:]
            ce_name = synth_fun.args[0]

            if ce_name not in candidate_dict:
                # Rosette will not return a function if no choice needs to be made
                candidate_dict[ce_name] = (
                    synth_fun.args[1]
                    .chooseArbitrarily()
                    .map_args(lambda expr: convert_expr(expr))
                )

            candidates_smt.append(
                FnDeclRecursive(
                    ce_name,
                    synth_fun.body().type,
                    candidate_dict[ce_name],
                    *all_vars,
                )
            )

        all_candidates_by_name = {c.name(): c for c in candidates_smt}
        # Prune ite branches
        all_candidates_by_name = prune_fn_decls(all_candidates_by_name)
        # This is basically a list of synthesized functions.
        candidates_smt = list(all_candidates_by_name.values())

        ##### verification of synthesized ps/inv
        if log:
            print(f"====== verification of round {curr_sol_idx} solution ======")

        verify_logs: typing.List[str] = []

        if no_verify:
            if log:
                print("Not verifying solution")
            result_verify = "unsat"
        else:
            try:
                result_verify, verify_logs = verify_synth_result(
                    basename,
                    target_lang,
                    vars,
                    preds,
                    vc,
                    loop_and_ps_info,
                    cvc_path,
                    synth_dir,
                    candidates_smt,
                    candidate_dict,
                    fnsType,
                    uid=curr_sol_idx,
                    use_rosette=False,
                )
            except CVC5UnsupportedException:
                print("WARNING: USING LARGE BOUND ROSETTE FOR VERIFICATION")
                result_verify, verify_logs = verify_synth_result(
                    basename,
                    target_lang,
                    vars,
                    preds,
                    vc,
                    loop_and_ps_info,
                    cvc_path,
                    synth_dir,
                    candidates_smt,
                    candidate_dict,
                    fnsType,
                    uid,
                    use_rosette=True,
                )

        if not no_verify and log:
            print("Verification Output:", result_verify)

        if result_verify == "unsat":
            if log:
                if not no_verify:
                    print(
                        "Verified PS and INV Candidates ",
                        "\n\n".join([str(c) for c in candidates_smt]),
                    )
                else:
                    print("Synthesized PS and INV Candidates\n")
                    for candidate in candidates_smt:
                        print(
                            f"def {candidate.name()}({', '.join([a.args[0] for a in candidate.arguments()])})"
                        )
                        body = candidate.body()
                        if isinstance(body, str):
                            print(body)
                        else:
                            print(codegen(body))
                        print("\n\n")
            # Kill the process, since we have already found the solution
            proc_synthesis.terminate()
            return candidates_smt
        else:
            if log:
                print(
                    "verification failed",
                    "\n\n".join([str(c) for c in candidates_smt]),
                )
                print("\n".join(verify_logs))
                print("\nProceeding to verifying the next solution")
            if last_processed_sol_idx + 1 == rounds_to_guess:
                raise VerificationFailed("Verification failed")

        last_processed_sol_idx = curr_sol_idx

        # exit_code = proc_synthesis.poll()

    # Now we have exited out of the while loop
    if exit_code != 0:
        if len(result_synth) > 0 and result_synth[0] == "#f":
            raise SynthesisFailed(f"Synthesis failed: exit code {exit_code}")
        else:
            raise Exception(
                f"Rosette failed: exit code {exit_code}\n" + "\n".join(err_synth)
            )
