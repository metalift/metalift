import os
import subprocess
import typing
from importlib import resources
from typing import IO, Any, Callable, Dict, List, Union

import pyparsing as pp

from metalift import process_tracker, utils
from metalift.analysis import CodeInfo
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
from metalift.ir import Lt, Mul, Not, ObjectT, Or
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
from metalift.rosette_translator import toRosette
from metalift.synthesis_common import (
    SynthesisFailed,
    VerificationFailed,
    generateTypes,
    verify_synth_result,
)

# TODO: remove after proper replacement
from metalift.types import CVC5UnsupportedException, FnT, MapT
from tests.python.utils.utils import codegen


# utils for converting rosette output to IR
# TODO: mypy 0.95 says parseString returns Any instead of ParseResults despite what pyparse's doc says
def generateAST(expr: str) -> Union[Any, pp.ParseResults]:
    s_expr = pp.nestedExpr(opener="(", closer=")")
    parser = pp.ZeroOrMore(s_expr)
    try:
        ast = parser.parseString(expr, parseAll=True).asList()
    except:
        raise Exception(f"Failed to parse Rosette output: {expr}")
    return ast


def parseOutput(resultSynth: typing.List[str]) -> typing.List[str]:
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


def toExpr(
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
    }
    expr_uni = {"!": Not}
    if isinstance(ast, list):
        if ast[0] == "define":
            return toExpr(ast[2], fnsType, varType, choices)
        elif ast[0] == "choose":
            # TODO(shadaj): now that we have chooseArbitrarily we could parse things properly
            return toExpr(ast[1], fnsType, varType, choices)
        elif ast[0] in expr_bi.keys():
            return expr_bi[ast[0]](
                *[toExpr(ast[i], fnsType, varType, choices) for i in range(1, len(ast))]
            )
        elif ast[0] in expr_uni.keys():
            return expr_uni[ast[0]](toExpr(ast[1], fnsType, varType, choices))
        elif ast[0] == "if":
            v1 = toExpr(ast[2], fnsType, varType, choices)
            v2 = toExpr(ast[3], fnsType, varType, choices)

            if v1.type == None:
                v1.type = v2.type
            if v2.type == None:
                v2.type = v1.type

            return Ite(
                toExpr(ast[1], fnsType, varType, choices),
                v1,
                v2,
            )
        elif ast[0] == "=":
            return Eq(
                toExpr(ast[1], fnsType, varType, choices),
                toExpr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "length":
            return Call("list_length", Int, toExpr(ast[1], fnsType, varType, choices))
        elif ast[0] == "list-list-length":
            return Call(
                "list_list_length", Int, toExpr(ast[1], fnsType, varType, choices)
            )
        elif ast[0] == "list-empty":
            return Call("list_empty", mlList[Int])
        elif ast[0] == "list-list-empty":
            return Call("list_list_empty", mlList[mlList[Int]])
        elif ast[0] == "list-append":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            elem = toExpr(ast[2], fnsType, varType, choices)
            return Call(
                "list_append",
                list_expr.type,
                list_expr,
                elem,
            )
        elif ast[0] == "list-list-append":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            elem = toExpr(ast[2], fnsType, varType, choices)
            return Call(
                "list_list_append",
                list_expr.type,
                list_expr,
                elem,
            )
        elif ast[0] == "list-prepend":
            elem = toExpr(ast[1], fnsType, varType, choices)
            lst = toExpr(ast[2], fnsType, varType, choices)
            return Call(
                "list_prepend",
                lst.type,
                elem,
                lst,
            )
        elif ast[0] == "list-list-prepend":
            elem = toExpr(ast[1], fnsType, varType, choices)
            lst = toExpr(ast[2], fnsType, varType, choices)
            return Call(
                "list_list_prepend",
                lst.type,
                elem,
                lst,
            )
        elif ast[0] == "list-ref-noerr":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call(
                "list_get",
                get_list_element_type(list_expr.type),
                list_expr,
                toExpr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "list-list-ref-noerr":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call(
                "list_list_get",
                get_list_element_type(list_expr.type),
                list_expr,
                toExpr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "list-tail-noerr":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call(
                "list_tail",
                list_expr.type,
                list_expr,
                toExpr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "list-list-tail-noerr":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call(
                "list_list_tail",
                list_expr.type,
                list_expr,
                toExpr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "list-concat":
            lst1 = toExpr(ast[1], fnsType, varType, choices)
            lst2 = toExpr(ast[2], fnsType, varType, choices)
            return Call("list_concat", lst1.type, lst1, lst2)
        elif ast[0] == "list-take-noerr":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call(
                "list_take",
                list_expr.type,
                list_expr,
                toExpr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "list-list-take-noerr":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call(
                "list_list_take",
                list_expr.type,
                list_expr,
                toExpr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "list-slice-noerr":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call(
                "list_slice",
                list_expr.type,
                list_expr,
                toExpr(ast[2], fnsType, varType, choices),
                toExpr(ast[3], fnsType, varType, choices),
            )
        elif ast[0] == "list-list-slice-noerr":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call(
                "list_list_slice",
                list_expr.type,
                list_expr,
                toExpr(ast[2], fnsType, varType, choices),
                toExpr(ast[3], fnsType, varType, choices),
            )
        elif ast[0] == "list-slice-with-length-noerr":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call(
                "list_slice_with_length",
                list_expr.type,
                list_expr,
                toExpr(ast[2], fnsType, varType, choices),
                toExpr(ast[3], fnsType, varType, choices),
            )
        elif ast[0] == "list-list-slice-with-length-noerr":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call(
                "list_list_slice_with_length",
                list_expr.type,
                list_expr,
                toExpr(ast[2], fnsType, varType, choices),
                toExpr(ast[3], fnsType, varType, choices),
            )
        elif ast[0] == "list-list-col-slice-noerr":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call(
                "list_list_col_slice",
                list_expr.type,
                list_expr,
                toExpr(ast[2], fnsType, varType, choices),
                toExpr(ast[3], fnsType, varType, choices),
            )
        elif ast[0] == "list-list-col-slice-with-length-noerr":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call(
                "list_list_col_slice_with_length",
                list_expr.type,
                list_expr,
                toExpr(ast[2], fnsType, varType, choices),
                toExpr(ast[3], fnsType, varType, choices),
            )
        elif ast[0] == "matrix-transpose-noerr":
            matrix_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call("matrix_transpose", matrix_expr.type, matrix_expr)
        elif ast[0] == "integer-sqrt":
            int_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call("integer_sqrt", Int, int_expr)
        elif ast[0] == "integer-exp":
            int_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call("integer_exp", Int, int_expr)
        elif ast[0] == "make-tuple":
            arg_eval = []
            for alen in range(1, len(ast)):
                arg_eval.append(toExpr(ast[alen], fnsType, varType, choices))
            return TupleExpr(*arg_eval)
        elif ast[0] == "tupleGet":
            return TupleGet(
                toExpr(ast[1], fnsType, varType, choices),
                toExpr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "set-create":
            return Call(ast[0], mlSet[Int])
        elif ast[0] == "set-insert":
            v = toExpr(ast[1], fnsType, varType, choices)
            s1 = toExpr(ast[2], fnsType, varType, choices)
            return Call(ast[0], mlSet[v.type], v, s1)  # type: ignore
        elif ast[0] == "set-singleton":
            v = toExpr(ast[1], fnsType, varType, choices)
            return Call(ast[0], mlSet[v.type], v)  # type: ignore
        elif ast[0] == "set-eq":
            s1 = toExpr(ast[1], fnsType, varType, choices)
            s2 = toExpr(ast[2], fnsType, varType, choices)
            return Eq(s1, s2)
        elif ast[0] == "set-union" or ast[0] == "set-minus":
            s1 = toExpr(ast[1], fnsType, varType, choices)
            s2 = toExpr(ast[2], fnsType, varType, choices)
            return Call(ast[0], s1.type, s1, s2)
        elif ast[0] == "set-subset":
            s1 = toExpr(ast[1], fnsType, varType, choices)
            s2 = toExpr(ast[2], fnsType, varType, choices)
            return Call(ast[0], Bool, s1, s2)
        elif ast[0] == "set-member":
            v = toExpr(ast[1], fnsType, varType, choices)
            s = toExpr(ast[2], fnsType, varType, choices)
            return Call(ast[0], Bool, v, s)
        elif ast[0] == "map-union":
            m1 = toExpr(ast[1], fnsType, varType, choices)
            m2 = toExpr(ast[2], fnsType, varType, choices)

            if m1.type == None:
                m1.type = m2.type
            if m2.type == None:
                m2.type = m1.type

            uf = toExpr(
                ast[3],
                fnsType,
                varType,
                choices,
                typeHint=FnT(m1.type.args[1], m1.type.args[1], m1.type.args[1]),  # type: ignore
            )

            return Call(ast[0], m1.type, m1, m2, uf)
        elif ast[0] == "map-values":
            m = toExpr(ast[1], fnsType, varType, choices)
            return Call(ast[0], mlList[m.type.args[1]], m)  # type: ignore
        elif ast[0] == "map-singleton":
            k = toExpr(ast[1], fnsType, varType, choices)
            v = toExpr(ast[2], fnsType, varType, choices)
            return Call(ast[0], MapT(k.type, v.type), k, v)  # type: ignore
        elif ast[0] == "map-create":
            return Call(ast[0], MapT(None, None))  # type: ignore
        elif ast[0] == "map-get":
            m = toExpr(ast[1], fnsType, varType, choices)
            k = toExpr(ast[2], fnsType, varType, choices)
            default = toExpr(ast[3], fnsType, varType, choices)
            return Call(ast[0], m.type.args[1], m, k, default)  # type: ignore
        elif ast[0] == "lambda":
            arg_list = [
                Var(n, t) for (t, n) in zip(typeHint.args[1:], ast[1])  # type: ignore
            ]

            varTypeUpdated = dict(varType)
            for a in arg_list:
                varTypeUpdated[a.args[0]] = a.type

            body = toExpr(ast[2], fnsType, varTypeUpdated, choices)
            return Lambda(body.type, body, *arg_list)  # type: ignore
        elif ast[0] == "let":
            var_value = toExpr(ast[1][0][1], fnsType, varType, choices)
            tmp_var_type = dict(varType)
            tmp_var_type[ast[1][0][0]] = var_value.type
            return Let(
                Var(ast[1][0][0], var_value.type),
                var_value,
                toExpr(ast[2], fnsType, tmp_var_type, choices),
            )
        elif ast[0] == "reduce_int":
            data = toExpr(ast[1], fnsType, varType, choices)
            fn = toExpr(
                ast[2],
                fnsType,
                varType,
                choices,
                typeHint=FnT(Int, data.type.args[0], Int),  # type: ignore
            )
            initial = toExpr(ast[3], fnsType, varType, choices)
            return Call("reduce_int", Int, data, fn, initial)
        elif ast[0] == "reduce_bool":
            data = toExpr(ast[1], fnsType, varType, choices)
            fn = toExpr(
                ast[2],
                fnsType,
                varType,
                choices,
                typeHint=FnT(Bool, data.type.args[0], Bool),  # type: ignore
            )
            initial = toExpr(ast[3], fnsType, varType, choices)
            return Call("reduce_bool", Bool, data, fn, initial)
        elif ast[0] in fnsType.keys():
            arg_eval = []
            ret_type = get_fn_return_type(fnsType[ast[0]])
            for alen in range(1, len(ast)):
                arg_eval.append(
                    toExpr(
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
            picked: Expr = choices[ast[0]].args[0]
            while (
                # picked.kind == Expr.Kind.Var
                isinstance(picked, Var)
                and picked.args[0].startswith("(")
                and picked.args[0][1:-1] in choices
            ):
                picked = choices[picked.args[0][1:-1]].args[0]
            return picked
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


def toSynthesize(
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
    targetLang: typing.Sequence[Union[FnDeclRecursive, FnDecl, Axiom]],
    vars: typing.Set[Var],
    invAndPs: typing.List[Synth],
    preds: typing.List[Expr],
    vc: Expr,
    loopAndPsInfo: typing.Sequence[Union[CodeInfo, Expr]],
    cvcPath: str = "cvc5",
    uid: int = 1,
    noVerify: bool = False,
    unboundedInts: bool = False,
    optimize_vc_equality: bool = False,
    listBound: int = 2,
    log: bool = True,
    uninterp_fns: List[str] = [],
    rounds_to_guess: int = 0,
    fns_to_guess: List[FnDeclRecursive] = [],
    fn_defs_to_exclude: List[FnDeclRecursive] = [],
) -> typing.List[FnDeclRecursive]:
    synthDir = "./synthesisLogs/"
    if not os.path.exists(synthDir):
        os.mkdir(synthDir)
    while True:
        # synthFile = synthDir + basename + f"_{uid}" + ".rkt"
        synthFile = synthDir + basename + ".rkt"

        with open(synthDir + "utils.rkt", "w") as out:
            out.write(resources.read_text(utils, "utils.rkt"))
        with open(synthDir + "bounded.rkt", "w") as out:
            out.write(resources.read_text(utils, "bounded.rkt"))

        if optimize_vc_equality:
            prev_vc = vc.toSMT()
            new_vars: typing.Set[Var] = set()
            while True:
                expr_count: Dict[str, int] = {}

                vc.src.countVariableUses(expr_count)  # type: ignore

                vc = vc.src.optimizeUselessEquality(expr_count, new_vars)  # type: ignore

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
        toRosette(
            filename=synthFile,
            targetLang=targetLang,
            vars=vars,
            invAndPs=invAndPs,
            preds=preds,
            vc=vc,
            loopAndPsInfo=loopAndPsInfo,
            rounds_to_guess=rounds_to_guess,
            fns_to_guess=fns_to_guess,
            fn_defs_to_exclude=fn_defs_to_exclude,
            unboundedInts=unboundedInts,
            listBound=listBound,
            writeChoicesTo=choices,
            uninterp_fns=uninterp_fns,
        )

        synthNames = toSynthesize(loopAndPsInfo, targetLang)
        procSynthesis = subprocess.Popen(
            ["racket", synthFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )
        process_tracker.all_processes.append(procSynthesis)

        try:
            resultSynth = [
                l.decode("utf-8").rstrip("\n")
                for l in typing.cast(IO[bytes], procSynthesis.stdout).readlines()
            ]

            errSynth = [
                l.decode("utf-8").rstrip("\n")
                for l in typing.cast(IO[bytes], procSynthesis.stderr).readlines()
            ]

            exitCode = procSynthesis.wait()
            if exitCode != 0:
                if len(resultSynth) > 0 and resultSynth[0] == "#f":
                    raise SynthesisFailed(f"Synthesis failed: exit code {exitCode}")
                else:
                    raise Exception(
                        f"Rosette failed: exit code {exitCode}\n" + "\n".join(errSynth)
                    )

            ##### End of Synthesis #####

            #####parsing output of rosette synthesis#####
            varTypes = {}
            for i in [*loopAndPsInfo, *invAndPs]:
                if isinstance(i, CodeInfo):
                    varTypes[i.name] = generateTypes(
                        i.modifiedVars + i.readVars + list(vars)
                    )
                else:
                    varTypes[i.args[0]] = generateTypes(i.args[2:])
            for l_i in targetLang:
                varTypes[l_i.args[0]] = generateTypes(l_i.args[2:])

            if resultSynth[0] == "#t":
                output = parseOutput(resultSynth[1:])
                candidateDict = {}
                fnsType = generateTypes(targetLang)
                for synthFun in invAndPs:
                    allVars = synthFun.args[2:]
                    ceName = synthFun.args[0]
                    fn_types = (synthFun.args[1].type, *[v.type for v in allVars])
                    fnsType[ceName] = Fn[typing.Tuple[fn_types]]  # type: ignore
                for n in synthNames:
                    for r in output:
                        if "define (" + n + " " in r or "define (" + n + ")" in r:
                            startIndex = r.find("(")
                            candidateDict[n] = toExpr(
                                generateAST(r[startIndex:])[0],
                                fnsType,
                                varTypes[n],
                                choices[n] if n in choices else {},
                            )
            else:
                raise SynthesisFailed("Synthesis failed")
            #####candidateDict --> definitions of all functions to be synthesized#####

            ##### generating function definitions of all the functions to be synthesized#####
            candidatesSMT: List[FnDeclRecursive] = []
            for synthFun in invAndPs:
                allVars = synthFun.args[2:]
                ceName = synthFun.args[0]

                if ceName not in candidateDict:
                    # Rosette will not return a function if no choice needs to be made
                    candidateDict[ceName] = synthFun.args[1].chooseArbitrarily()

                candidatesSMT.append(
                    FnDeclRecursive(
                        ceName,
                        synthFun.body().type,
                        candidateDict[ceName],
                        *allVars,
                    )
                )

            ##### verification of synthesized ps/inv
            if log:
                print("====== verification")

            verifyLogs: typing.List[str] = []

            if noVerify:
                if log:
                    print("Not verifying solution")
                resultVerify = "unsat"
            else:
                try:
                    resultVerify, verifyLogs = verify_synth_result(
                        basename,
                        targetLang,
                        vars,
                        preds,
                        vc,
                        loopAndPsInfo,
                        cvcPath,
                        synthDir,
                        candidatesSMT,
                        candidateDict,
                        fnsType,
                        uid,
                        useRosette=False,
                    )
                except CVC5UnsupportedException:
                    print("WARNING: USING LARGE BOUND ROSETTE FOR VERIFICATION")
                    resultVerify, verifyLogs = verify_synth_result(
                        basename,
                        targetLang,
                        vars,
                        preds,
                        vc,
                        loopAndPsInfo,
                        cvcPath,
                        synthDir,
                        candidatesSMT,
                        candidateDict,
                        fnsType,
                        uid,
                        useRosette=True,
                    )

            if not noVerify and log:
                print("Verification Output:", resultVerify)

            if resultVerify == "unsat":
                if log:
                    if not noVerify:
                        print(
                            "Verified PS and INV Candidates ",
                            "\n\n".join([str(c) for c in candidatesSMT]),
                        )
                    else:
                        print("Synthesized PS and INV Candidates\n")
                        for candidate in candidatesSMT:
                            print(
                                f"def {candidate.name()}({' '.join([a.args[0] for a in candidate.arguments()])})"
                            )
                            body = candidate.body()
                            if isinstance(body, str):
                                print(body)
                            else:
                                print(codegen(body))
                            print("\n\n")
                return candidatesSMT
            else:
                if log:
                    print(
                        "verification failed",
                        "\n\n".join([str(c) for c in candidatesSMT]),
                    )
                    print("\n".join(verifyLogs))
                    # inv_guess.append(resultSynth[1])
                    # print(inv_guess)
                raise VerificationFailed("Verification failed")
        finally:
            procSynthesis.terminate()
            procSynthesis.wait()
