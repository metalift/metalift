from ir import *

import typing
from typing import Any, Union


def filterArgs(argList: typing.List[Expr]) -> typing.List[Expr]:
    newArgs = []
    for a in argList:
        if a.type.name != "Function":
            newArgs.append(a)
    return newArgs


def filterBody(funDef: Expr, funCall: str, inCall: str) -> Expr:
    if funDef.kind.value in [
        "+",
        "-",
        "*",
        "=",
        "<",
        "=",
        ">=",
        "<=",
        "and",
        "or",
        "=>",
    ]:
        newArgs = [
            filterBody(funDef.args[0], funCall, inCall),
            filterBody(funDef.args[1], funCall, inCall),
        ]
        return Expr(funDef.kind, funDef.type, newArgs)
    elif funDef.kind.value == "not":
        return Not(filterBody(funDef.args[0], funCall, inCall))
    elif funDef.kind.value == "ite":
        return Ite(
            filterBody(funDef.args[0], funCall, inCall),
            filterBody(funDef.args[1], funCall, inCall),
            filterBody(funDef.args[2], funCall, inCall),
        )

    elif funDef.kind.value == "call":

        if funDef.type.name == "Function":
            newArgs = []

            for i in range(1, len(funDef.args)):
                newArgs.append(filterBody(funDef.args[i], funCall, inCall))
            return Call(inCall, funDef.type, *newArgs)

        elif funDef.args[0] == funCall:
            newArgs = []
            for i in range(1, len(funDef.args)):
                if funDef.args[i].type.name != "Function":
                    newArgs.append(filterBody(funDef.args[i], funCall, inCall))
            return Call(funCall + "_" + inCall, funDef.type, *newArgs)
        else:
            newArgs = []
            for i in range(1, len(funDef.args)):
                newArgs.append(filterBody(funDef.args[i], funCall, inCall))
            return Call(funDef.args[0], funDef.type, *newArgs)
    else:
        return funDef


def toSMT(
    targetLang: typing.List[Any],
    vars: typing.Set[Expr],
    invAndPs: typing.List[Expr],
    preds: Union[str, typing.List[Any]],
    vc: Expr,
    outFile: str,
    inCalls: typing.List[Any],
    fnCalls: typing.List[Any],
    isSynthesis: bool = False,
) -> None:
    # order of appearance: inv and ps grammars, vars, non inv and ps preds, vc
    with open(outFile, mode="w") as out:
        if not isSynthesis:
            out.write(open("./utils/list-axioms.smt", "r").read())

        out.write("\n\n".join([str(t) for t in targetLang]))
        if inCalls:
            fnDecls = []
            for i in inCalls:
                for t in targetLang:
                    if i[0] == t.args[0]:
                        # parse body
                        newBody = filterBody(t.args[1], i[0], i[1])

                        # remove function type args
                        newArgs = filterArgs(t.args[2:])
                        fnDecls.append(
                            FnDecl(t.args[0] + "_" + i[1], t.type, newBody, *newArgs)
                        )

            candidates = []

            for cand in invAndPs:
                newBody = cand.args[1]
                for idx, i in enumerate(inCalls):
                    newBody = filterBody(newBody, i[0], i[1])
                candidates.append(
                    FnDecl(cand.args[0], cand.type, newBody, *cand.args[2:])
                )
            out.write("\n\n".join(["\n%s\n" % (cand) for cand in candidates]))
        elif fnCalls:
            out.write("\n\n".join(["\n%s\n" % (cand) for cand in invAndPs]))
        else:
            if isinstance(invAndPs, str):
                out.write("\n\n%s\n\n" % invAndPs)
            else:
                out.write("\n\n".join(["\n%s\n" % (cand) for cand in invAndPs]))

        declarations: typing.List[typing.Tuple[str, Type]] = []
        for v in vars:
            genVar(v, declarations)

        var_decl_command = "declare-var" if isSynthesis else "declare-const"
        out.write(
            "\n%s\n\n"
            % "\n".join(
                ["(%s %s %s)" % (var_decl_command, v[0], v[1]) for v in declarations]
            )
        )

        ##### ToDo write axioms using the construct
        if "count" in outFile:
            out.write(open("./utils/map_reduce_axioms.txt", "r").read())

        if isinstance(preds, str):
            out.write("%s\n\n" % preds)

        # a list of Exprs - print name, args, return type
        elif isinstance(preds, list):
            preds = "\n".join(
                [
                    "(define-fun %s (%s) (%s) )"
                    % (
                        p.args[0],
                        " ".join("(%s %s)" % (a.args[0], a.type) for a in p.args[1:]),
                        p.type,
                    )
                    for p in preds
                ]
            )
            out.write("%s\n\n" % preds)

        else:
            raise Exception("unknown type passed in for preds: %s" % preds)

        if isSynthesis:
            out.write("%s\n\n" % Constraint(vc))
            out.write("(check-synth)")
        else:
            out.write("%s\n\n" % MLInst_Assert(Not(vc)))
            out.write("(check-sat)\n(get-model)")
