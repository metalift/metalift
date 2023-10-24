from inspect import isclass
import typing
from metalift.analysis import CodeInfo
import pyparsing as pp
from metalift import ir
from metalift.ir import BoolObject, Expr, FnDeclRecursive, FnDecl, IntObject, Var, ListObject
from llvmlite.binding import ValueRef
from typing import Any, Dict, List, Sequence, Set, Tuple, Union, Optional, get_args

from metalift.ir_util import is_list_type_expr, is_set_type_expr


# TODO: mypy 0.95 says parseString returns Any instead of ParseResults despite what pyparse's doc says
def generateAST(expr: str) -> Union[List[Any], pp.ParseResults]:
    s_expr = pp.nestedExpr(opener="(", closer=")")
    parser = pp.ZeroOrMore(s_expr)
    ast = parser.parseString(expr, parseAll=True).asList()
    return ast


def genVar(v: Expr, decls: List[str], vars_all: List[str], listBound: int) -> None:
    if v.type == IntObject:
    # if (
    #     # v.type.name == "Int"
    #     # or v.type.name == "ClockInt"
    #     # or v.type.name == "EnumInt"
    #     # or v.type.name == "OpaqueInt"
    #     # or v.type.name == "NodeIDInt"
    #     type_name == "Int"
    # ):
        decls.append("(define-symbolic %s integer?)" % v.toRosette())
        vars_all.append(v.args[0])

    elif v.type == BoolObject:
        decls.append("(define-symbolic %s boolean?)" % v.toRosette())
        vars_all.append(v.args[0])

    elif is_list_type_expr(v) or is_set_type_expr(v): #v.type.name == "MLList" or v.type.name == "Set":
        tmp = [v.args[0] + "_BOUNDEDSET-" + str(i) for i in range(listBound)]

        for t in tmp:
            genVar(Var(t, typing.get_args(v.type)[0]), decls, vars_all, listBound)

        len_name = v.args[0] + "_BOUNDEDSET-len"
        genVar(Var(len_name, ir.IntObject), decls, vars_all, listBound)

        if type_name == "Set":
            decls.append(
                "(define %s (sort (remove-duplicates (take %s %s)) <))"
                % (v.args[0], "(list " + " ".join(tmp[:listBound]) + ")", len_name)
            )
            decls.append(decl)
        else:
            decls.append(
                "(define %s (take %s %s))"
                % (v.args[0], "(list " + " ".join(tmp[:listBound]) + ")", len_name)
            )
    elif type_name == "Tuple":
        elem_names = []
        for i, t in enumerate(typing.get_args(v.type)):
            elem_name = v.args[0] + "_TUPLE-" + str(i)
            genVar(Var(elem_name, t), decls, vars_all, listBound)
            elem_names.append(elem_name)

        decls.append("(define %s (list %s))" % (v.args[0], " ".join(elem_names)))
    #TODO: change this once MapObject is ready
    elif hasattr(v.type, "name") and v.type.name == "Map":
        tmp_k = [v.args[0] + "_MAP-" + str(i) + "-k" for i in range(listBound)]
        tmp_v = [v.args[0] + "_MAP-" + str(i) + "-v" for i in range(listBound)]
        for t in tmp_k:
            # TODO: v.type no longer has args, find proper solution
            genVar(Var(t, v.type.args[0]), decls, vars_all, listBound)  # type: ignore
        for t in tmp_v:
            # TODO: v.type no longer has args, find proper solution
            genVar(Var(t, v.type.args[1]), decls, vars_all, listBound)  # type: ignore

        len_name = v.args[0] + "-len"
        genVar(Var(len_name, Int), decls, vars_all, listBound)

        all_pairs = ["(cons %s %s)" % (k, v) for k, v in zip(tmp_k, tmp_v)]

        decls.append(
            "(define %s (map-normalize (take %s %s)))"
            % (v.args[0], "(list " + " ".join(all_pairs[:listBound]) + ")", len_name)
        )
    else:
        raise Exception(f"Unknown type: {v.type}")


def generateVars(vars: Set[Var], listBound: int) -> Tuple[str, List[str]]:
    decls: List[str] = []
    vars_all: List[str] = []
    sorted_vars = list(vars)
    sorted_vars.sort(key=lambda v: v.name())
    for v in sorted_vars:
        genVar(v, decls, vars_all, listBound)

    return "\n".join(decls), vars_all


def generateSynth(
    vars: List[str],
    invariant_guesses: List[Any],
) -> str:
    listvars = "(list " + " ".join(vars) + ")"
    if invariant_guesses:
        blocking_constraints = []
        for inv in invariant_guesses:
            blocking_constraints.append("(assert (!(eq? inv %s)))" % inv.toRosette())
        asserts = " ".join(blocking_constraints)
        synth_fun = (
            "(define sol\n (synthesize\n #:forall %s\n #:guarantee (begin (assertions) %s)))\n (sat? sol)\n %s"
            % (listvars, asserts, "(print-forms sol)")
        )
    else:
        synth_fun = (
            "(define sol\n (synthesize\n #:forall %s\n #:guarantee (assertions)))\n (sat? sol)\n %s"
            % (listvars, "(print-forms sol)")
        )
    return synth_fun


def generateInvPs(loopAndPsInfo: Sequence[Union[CodeInfo, Expr]]) -> str:
    decls = ""
    for i in loopAndPsInfo:
        all_args = (
            i.modifiedVars + i.readVars if isinstance(i, CodeInfo) else i.args[2:]
        )
        func_name = i.name if isinstance(i, CodeInfo) else i.args[0]
        arg_names = " ".join(
            [a.name if isinstance(a, ValueRef) else a.toRosette() for a in all_args]
        )
        decls += "(define (%s %s) (%s %s #:depth 10))\n" % (
            func_name,
            arg_names,
            func_name + "_gram",
            arg_names,
        )
    return decls


def toRosette(
    filename: str,
    targetLang: Sequence[Union[FnDeclRecursive, FnDecl, ir.Axiom]],
    vars: Set[Var],
    invAndPs: typing.Sequence[Union[FnDeclRecursive, ir.Synth]],
    preds: List[Expr],
    vc: BoolObject,
    loopAndPsInfo: Sequence[Union[CodeInfo, Expr]],
    invGuess: List[Any],
    unboundedInts: bool,
    listBound: int,
    writeChoicesTo: Optional[Dict[str, Dict[str, Expr]]] = None,
    verifyMode: bool = False,
    uninterp_fns: List[str] = [],
) -> None:
    f = open(filename, "w")
    print(
        "#lang rosette\n"
        + '(require "./bounded.rkt")\n'
        + '(require "./utils.rkt")\n'
        + "(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)\n\n",
        file=f,
    )

    # struct declarations and function definition of target constructs
    for t in targetLang:
        is_uninterp_fn = (
            isinstance(t, FnDecl) or isinstance(t, FnDeclRecursive)
        ) and t.name() in uninterp_fns
        if t.args[1] is None and not is_uninterp_fn:
            continue
        print("\n", t.toRosette(is_uninterp=is_uninterp_fn), "\n", file=f)
    # print(generateInter(targetLang),file=f)

    # inv and ps grammar definition
    for g in invAndPs:
        writeTo = None
        if writeChoicesTo != None:
            writeChoicesTo[g.args[0]] = {}  # type: ignore
            writeTo = writeChoicesTo[g.args[0]]  # type: ignore
        print(g.toRosette(writeTo), "\n", file=f)

    # inv and ps declaration
    print(generateInvPs(loopAndPsInfo), file=f)

    fnsDecls = []
    for t in targetLang:
        if (
            t.args[1] is None
            and (isinstance(t, FnDecl) or isinstance(t, FnDeclRecursive))
            and t.name() not in uninterp_fns
        ):
            fnsDecls.append(t)
    if fnsDecls:
        print(generateInvPs(fnsDecls), file=f)

    # vars declaration
    varDecls, vars_all = generateVars(vars, listBound)
    print(varDecls, file=f)

    # Vc definition
    if unboundedInts:
        print("(current-bitwidth #f)", file=f)
    else:
        print("(current-bitwidth %d)" % (6), file=f)

    print("(define (assertions)\n (assert %s))\n" % vc.toRosette(), file=f)

    # synthesis function
    if not verifyMode:
        print(generateSynth(vars_all, invGuess), file=f)
    else:
        print("(verify (assertions))", file=f)
    f.close()
