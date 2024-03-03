import typing
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple, Union

import pyparsing as pp
from llvmlite.binding import ValueRef

from metalift import ir
from metalift.analysis import CodeInfo
from metalift.ir import (
    Bool,
    Expr,
    FnDecl,
    FnDeclRecursive,
    Int,
    Var,
    get_matrix_element_type,
    get_nested_list_element_type,
    is_list_type,
    is_matrix_type,
    is_nested_list_type,
    is_set_type,
    is_tuple_type,
)


# TODO: mypy 0.95 says parseString returns Any instead of ParseResults despite what pyparse's doc says
def generate_ast(expr: str) -> Union[List[Any], pp.ParseResults]:
    s_expr = pp.nestedExpr(opener="(", closer=")")
    parser = pp.ZeroOrMore(s_expr)
    ast = parser.parseString(expr, parseAll=True).asList()
    return ast


def gen_var(v: Expr, decls: List[str], vars_all: List[str], listBound: int) -> None:
    if v.type == Int:
        decls.append("(define-symbolic %s integer?)" % v.to_rosette())
        vars_all.append(v.args[0])

    elif v.type == Bool:
        decls.append("(define-symbolic %s boolean?)" % v.to_rosette())
        vars_all.append(v.args[0])

    elif is_matrix_type(v.type):
        len_name = v.args[0] + "_BOUNDEDSET-len"
        gen_var(Var(len_name, ir.Int), decls, vars_all, listBound)

        tmp = [
            v.args[0] + "_BOUNDEDSET-" + str(i) for i in range(listBound * listBound)
        ]
        nested_element_type = get_matrix_element_type(v.type)
        for t in tmp:
            gen_var(Var(t, nested_element_type), decls, vars_all, listBound)
        nested_lsts: List[str] = [
            f"(list {' '.join(tmp[i : i + listBound])})"
            for i in range(0, len(tmp) - 1, listBound)
        ]
        decl = f"(define {v.args[0]} (take (list {' '.join(nested_lsts)}) {len_name}))"
        decls.append(decl)

    elif is_list_type(v.type) or is_set_type(v.type):
        len_name = v.args[0] + "_BOUNDEDSET-len"
        gen_var(Var(len_name, ir.Int), decls, vars_all, listBound)

        is_nested_list = is_nested_list_type(v.type)
        if is_nested_list:
            tmp = [
                v.args[0] + "_BOUNDEDSET-" + str(i)
                for i in range(listBound * listBound)
            ]
            nested_element_type = get_nested_list_element_type(v.type)
            for t in tmp:
                gen_var(Var(t, nested_element_type), decls, vars_all, listBound)
            nested_lsts: List[str] = [  # type: ignore
                f"(list {' '.join(tmp[i : i + listBound])})"
                for i in range(0, len(tmp) - 1, listBound)
            ]
            decl = (
                f"(define {v.args[0]} (take (list {' '.join(nested_lsts)}) {len_name}))"
            )
            decls.append(decl)
        else:
            tmp = [v.args[0] + "_BOUNDEDSET-" + str(i) for i in range(listBound)]

            for t in tmp:
                gen_var(Var(t, typing.get_args(v.type)[0]), decls, vars_all, listBound)

            if is_set_type(v.type):
                decls.append(
                    "(define %s (sort (remove-duplicates (take %s %s)) <))"
                    % (v.args[0], "(list " + " ".join(tmp[:listBound]) + ")", len_name)
                )
            else:
                decls.append(
                    "(define %s (take %s %s))"
                    % (v.args[0], "(list " + " ".join(tmp[:listBound]) + ")", len_name)
                )
    elif is_tuple_type(v.type):
        elem_names = []
        for i, t in enumerate(typing.get_args(v.type)):
            elem_name = v.args[0] + "_TUPLE-" + str(i)
            gen_var(Var(elem_name, t), decls, vars_all, listBound)
            elem_names.append(elem_name)

        decls.append("(define %s (list %s))" % (v.args[0], " ".join(elem_names)))
    # TODO: change this once MapObject is ready
    elif hasattr(v.type, "name") and v.type.name == "Map":
        tmp_k = [v.args[0] + "_MAP-" + str(i) + "-k" for i in range(listBound)]
        tmp_v = [v.args[0] + "_MAP-" + str(i) + "-v" for i in range(listBound)]
        for t in tmp_k:
            # TODO: v.type no longer has args, find proper solution
            gen_var(Var(t, v.type.args[0]), decls, vars_all, listBound)  # type: ignore
        for t in tmp_v:
            # TODO: v.type no longer has args, find proper solution
            gen_var(Var(t, v.type.args[1]), decls, vars_all, listBound)  # type: ignore

        len_name = v.args[0] + "-len"
        gen_var(Var(len_name, Int), decls, vars_all, listBound)

        all_pairs = ["(cons %s %s)" % (k, v) for k, v in zip(tmp_k, tmp_v)]

        decls.append(
            "(define %s (map-normalize (take %s %s)))"
            % (v.args[0], "(list " + " ".join(all_pairs[:listBound]) + ")", len_name)
        )
    else:
        raise Exception(f"Unknown type: {v.type}")


def generate_vars(vars: Set[Var], listBound: int) -> Tuple[str, List[str]]:
    decls: List[str] = []
    vars_all: List[str] = []
    sorted_vars = list(vars)
    sorted_vars.sort(key=lambda v: v.name())
    for v in sorted_vars:
        gen_var(v, decls, vars_all, listBound)

    return "\n".join(decls), vars_all


def generate_synth(
    vars: List[str],
    rounds_to_guess: int = 0,
    fns_to_guess: List[FnDeclRecursive] = [],
    fn_defs_to_exclude: List[FnDeclRecursive] = [],
) -> str:
    listvars = f"(list {' '.join(vars)})"
    if len(fn_defs_to_exclude) > 0:
        constraints = [
            f"(assert (!(eq? {f.name()} {f.to_rosette()})))" for f in fn_defs_to_exclude
        ]
        return f"""
        (define sol
            (synthesize
                #:forall {listvars}
                #:guarantee (begin
                    (assertions)
                    {' '.join(constraints)}
                )
            )
        )
        (sat? sol)
        (print-forms sol)
        """
    all_synth_funs: List[str] = []
    synth_fun = f"""
    (define sol0
        (synthesize
            #:forall {listvars}
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
    """
    all_synth_funs.append(synth_fun)
    for i in range(1, rounds_to_guess + 1):
        single_solution_constraints: List[Bool] = []
        for prev_i in range(i):
            round_i_constraints = []
            for guess in fns_to_guess:
                guess_call = f"({guess.name()} {' '.join(arg.name() for arg in guess.arguments())})"
                constraint = (
                    f"(! (eq? {guess_call} (evaluate {guess_call} sol{prev_i})))"
                )
                round_i_constraints.append(constraint)
            single_solution_constraints.append(
                f"(assume (|| {' '.join(round_i_constraints)}))"
            )
        synth_fun = f"""
        (define sol{i}
            (synthesize
                #:forall {listvars}
                #:guarantee (begin
                    {' '.join(single_solution_constraints)}
                    (assertions)
                )
            )
        )
        (sat? sol{i})
        (print-forms sol{i})
        """
        all_synth_funs.append(synth_fun)
    return "\n".join(all_synth_funs)


def generate_inv_ps(loop_and_ps_info: Sequence[Union[CodeInfo, Expr]]) -> str:
    decls = ""
    for i in loop_and_ps_info:
        all_args = (
            i.modified_vars + i.read_vars if isinstance(i, CodeInfo) else i.args[2:]
        )
        func_name = i.name if isinstance(i, CodeInfo) else i.args[0]
        arg_names = " ".join(
            [a.name if isinstance(a, ValueRef) else a.to_rosette() for a in all_args]
        )
        decls += "(define (%s %s) (%s %s #:depth 10))\n" % (
            func_name,
            arg_names,
            func_name + "_gram",
            arg_names,
        )
    return decls


def to_rosette(
    filename: str,
    target_lang: Sequence[Union[FnDeclRecursive, FnDecl, ir.Axiom]],
    vars: Set[Var],
    inv_and_ps: typing.Sequence[Union[FnDeclRecursive, ir.Synth]],
    preds: List[Expr],
    vc: Expr,
    loop_and_ps_info: Sequence[Union[CodeInfo, Expr]],
    rounds_to_guess: int,
    fns_to_guess: List[FnDeclRecursive],
    fn_defs_to_exclude: List[FnDeclRecursive],
    unbounded_ints: bool,
    list_bound: int,
    write_choices_to: Optional[Dict[str, Dict[str, Expr]]] = None,
    verify_mode: bool = False,
    uninterp_fns: List[str] = [],
) -> None:
    f = open(filename, "w")
    print(
        "#lang rosette\n"
        + '(require "./bounded.rkt")\n'
        + '(require "./utils.rkt")\n'
        + "(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)\n"
        + "(require rosette/solver/smt/bitwuzla)\n"
        + '(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash \':seed 0)))\n'
        + "\n",
        # + "(require rosette/solver/smt/z3)\n"
        # + "(current-solver (z3 #:options (hash ':random-seed 0)))\n"
        # + "\n",
        file=f,
    )

    # struct declarations and function definition of target constructs
    for t in target_lang:
        is_uninterp_fn = (
            isinstance(t, FnDecl) or isinstance(t, FnDeclRecursive)
        ) and t.name() in uninterp_fns
        if t.args[1] is None and not is_uninterp_fn:
            continue
        print("\n", t.to_rosette(is_uninterp=is_uninterp_fn), "\n", file=f)
    # print(generateInter(targetLang),file=f)

    # inv and ps grammar definition
    for g in inv_and_ps:
        writeTo = None
        if write_choices_to != None:
            write_choices_to[g.args[0]] = {}  # type: ignore
            writeTo = write_choices_to[g.args[0]]  # type: ignore
        print(g.to_rosette(writeTo), "\n", file=f)

    # inv and ps declaration
    print(generate_inv_ps(loop_and_ps_info), file=f)

    fnsDecls = []
    for t in target_lang:
        if (
            (isinstance(t, FnDecl) or isinstance(t, FnDeclRecursive))
            and t.body() is None
            and t.name() not in uninterp_fns
        ):
            fnsDecls.append(t)
    if fnsDecls:
        print(generate_inv_ps(fnsDecls), file=f)

    # vars declaration
    var_decls, vars_all = generate_vars(vars, list_bound)
    print(var_decls, file=f)

    # Vc definition
    if unbounded_ints:
        print("(current-bitwidth #f)", file=f)
    else:
        print("(current-bitwidth %d)" % (6), file=f)

    print("(define (assertions)\n (assert %s))\n" % vc.to_rosette(), file=f)

    # synthesis function
    if not verify_mode:
        print(
            generate_synth(vars_all, rounds_to_guess, fns_to_guess, fn_defs_to_exclude),
            file=f,
        )
    else:
        print("(verify (assertions))", file=f)
    f.close()
