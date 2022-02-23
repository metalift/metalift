from analysis import CodeInfo, analyze
import ir
import re
import pyparsing as pp
from ir import Expr, Var
from llvmlite.binding import ValueRef
from typing import Any, List, Sequence, Set, Tuple, Union

# param for bounding the input list length
n = 3


def generateAST(expr: str) -> List[Any]:
    s_expr = pp.nestedExpr(opener="(", closer=")")
    parser = pp.ZeroOrMore(s_expr)
    ast = parser.parseString(expr, parseAll=True).asList()
    return ast  # type: ignore


def genVar(v: Expr, decls: List[str], vars_all: List[str]) -> None:
    if v.type.name == "Int":
        decls.append("(define-symbolic %s integer?)" % v.toRosette())
        vars_all.append(v.args[0])

    elif v.type.name == "Bool":
        decls.append("(define-symbolic %s boolean?)" % v.toRosette())
        vars_all.append(v.args[0])

    elif v.type.name == "MLList" or v.type.name == "Set":
        tmp = [v.args[0] + "_" + str(i) for i in range(n)]
        tmp.append(v.args[0] + "-len")
        vars_all.extend(tmp)
        if v.type.args[0].name == "Int":
            decls.append("(define-symbolic %s integer?)" % (" ".join(tmp)))
        elif v.type.args[0].name == "Bool":
            decls.append("(define-symbolic %s boolean?)" % (" ".join(tmp)))

        if v.type.name == "Set":
            decls.append(
                "(define %s (sort (remove-duplicates (take %s %s)) <))"
                % (v.args[0], "(list " + " ".join(tmp[:n]) + ")", tmp[-1])
            )
        else:
            decls.append(
                "(define %s (take %s %s))"
                % (v.args[0], "(list " + " ".join(tmp[:n]) + ")", tmp[-1])
            )
    elif v.type.name == "Tuple":
        elem_names = []
        for i, t in enumerate(v.type.args):
            elem_name = v.args[0] + "_" + str(i)
            genVar(Var(elem_name, t), decls, vars_all)
            elem_names.append(elem_name)

        decls.append("(define %s (list %s))" % (v.args[0], " ".join(elem_names)))
    else:
        raise Exception(f"Unknown type: {v.type}")


def generateVars(vars: Set[Expr]) -> Tuple[str, List[str]]:
    decls: List[str] = []
    vars_all: List[str] = []
    for v in list(vars):
        genVar(v, decls, vars_all)

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
    targetLang: List[Expr],
    vars: Set[Expr],
    invAndPs: List[Expr],
    preds: List[Expr],
    vc: Expr,
    loopAndPsInfo: Sequence[Union[CodeInfo, Expr]],
    invGuess: List[Any],
    unboundedInts: bool,
) -> None:

    f = open(filename, "w")
    print(
        "#lang rosette\n"
        + '(require "../utils/bounded.rkt")\n'
        + '(require "../utils/utils.rkt")\n'
        + "(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)\n\n",
        file=f,
    )

    # struct declarations and function definition of target constructs
    for t in targetLang:
        if t.args[1] != "":
            print("\n", t.toRosette(), "\n", file=f)
    # print(generateInter(targetLang),file=f)

    # inv and ps grammar definition
    for g in invAndPs:
        print(g.toRosette(), "\n", file=f)

    # inv and ps declaration
    print(generateInvPs(loopAndPsInfo), file=f)

    fnsDecls = []
    for t in targetLang:
        if t.args[1] == "":
            fnsDecls.append(t)
    if fnsDecls:
        print(generateInvPs(fnsDecls), file=f)

    # vars declaration
    varDecls, vars_all = generateVars(vars)
    print(varDecls, file=f)

    # Vc definition
    if unboundedInts:
        print("(current-bitwidth #f)", file=f)
    else:
        print("(current-bitwidth %d)" % (6), file=f)

    print("(define (assertions)\n (assert %s))\n" % vc.toRosette(), file=f)

    # synthesis function
    print(generateSynth(vars_all, invGuess), file=f)
    f.close()

    # print(loopAndPsInfo)
