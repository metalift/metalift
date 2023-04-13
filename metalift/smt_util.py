import importlib.resources as resources
from metalift import utils

from metalift.ir import *
import typing
from typing import Any, Union


def filterArgs(argList: typing.List[Expr]) -> typing.List[Expr]:
    newArgs = []
    for a in argList:
        if a.type.name != "Function":
            newArgs.append(a)
    return newArgs


def filterBody(funDef: Expr, funCall: str, inCall: str) -> Expr:
    if (
        (not isinstance(funDef, Expr))
        or isinstance(funDef, Var)
        or isinstance(funDef, Lit)
    ):
        return funDef
    elif isinstance(funDef, Call) and funDef.args[0] == funCall:
        newArgs = []
        for i in range(1, len(funDef.args)):
            if funDef.args[i].type.name != "Function":
                newArgs.append(filterBody(funDef.args[i], funCall, inCall))
        return Call(funCall + "_" + inCall, funDef.type, *newArgs)
    elif isinstance(funDef, CallValue):
        newArgs = []

        for i in range(1, len(funDef.args)):
            newArgs.append(filterBody(funDef.args[i], funCall, inCall))
        return Call(inCall, funDef.type, *newArgs)
    else:
        return funDef.mapArgs(lambda x: filterBody(x, funCall, inCall))


def toSMT(
    targetLang: typing.Sequence[Any],
    vars: typing.Set[Var],
    invAndPs: typing.Sequence[Union[FnDeclRecursive, Synth]],
    preds: Union[str, typing.List[Any]],
    vc: Expr,
    outFile: str,
    inCalls: typing.List[Any],
    fnCalls: typing.List[Any],
    isSynthesis: bool = False,
) -> None:
    # order of appearance: inv and ps grammars, vars, non inv and ps preds, vc
    with open(outFile, mode="w") as out:
        out.write(resources.read_text(utils, "tuples.smt"))
        if not isSynthesis:
            out.write(resources.read_text(utils, "list-axioms.smt"))
            # out.write(resources.read_text(utils, "list-axioms-nested.smt"))
            out.write(resources.read_text(utils, "map-axioms.smt"))

        early_candidates_names = set()

        fnDecls = []
        axioms = []
        for t in targetLang:
            if (
                isinstance(t, FnDeclRecursive)
                or isinstance(t, FnDecl)
                # t.kind == Expr.Kind.FnDecl or t.kind == Expr.Kind.FnDeclNonRecursive
            ) and t.args[0] in fnCalls:
                found_inline = False
                for i in inCalls:
                    if i[0] == t.args[0]:
                        found_inline = True
                        early_candidates_names.add(i[1])
                        # parse body
                        newBody = filterBody(t.args[1], i[0], i[1])

                        # remove function type args
                        newArgs = filterArgs(t.args[2:])
                        fnDecls.append(
                            FnDeclRecursive(
                                t.args[0] + "_" + i[1],
                                t.type.args[0],
                                newBody,
                                *newArgs,
                            )
                            # if t.kind == Expr.Kind.FnDecl
                            if isinstance(t, FnDeclRecursive)
                            else FnDecl(
                                t.args[0] + "_" + i[1],
                                t.type.args[0],
                                newBody,
                                *newArgs,
                            )
                        )

                if not found_inline and t.args[1] != None:
                    out.write(t.toSMT() + "\n\n")
            # elif t.kind == Expr.Kind.Axiom:
            elif isinstance(t, Axiom):
                axioms.append(t)

        early_candidates = []
        candidates = []
        filtered_axioms = []

        for cand in invAndPs:
            newBody = cand.args[1]
            for i in inCalls:
                newBody = filterBody(newBody, i[0], i[1])

            # if cand.kind == Expr.Kind.Synth:
            if isinstance(cand, Synth):
                decl: Union[Synth, FnDeclRecursive] = Synth(
                    cand.args[0], newBody, *cand.args[2:]
                )
            else:
                decl = FnDeclRecursive(
                    cand.args[0], cand.type.args[0], newBody, *cand.args[2:]
                )

            if cand.args[0] in early_candidates_names:
                early_candidates.append(decl)
            else:
                candidates.append(decl)

        for axiom in axioms:
            newBody = axiom.args[0]
            for i in inCalls:
                newBody = filterBody(newBody, i[0], i[1])

            filtered_axioms.append(Axiom(newBody, *axiom.args[1:]))

        for i in inCalls:
            vc = filterBody(vc, i[0], i[1])

        out.write("\n\n".join(["\n%s\n" % cand.toSMT() for cand in early_candidates]))
        out.write("\n\n".join(["\n%s\n" % inlined.toSMT() for inlined in fnDecls]))
        out.write("\n\n".join(["\n%s\n" % axiom.toSMT() for axiom in filtered_axioms]))
        out.write("\n\n".join(["\n%s\n" % cand.toSMT() for cand in candidates]))

        declarations: typing.List[typing.Tuple[str, Type]] = []
        for v in vars:
            declarations.append((v.args[0], v.type))

        var_decl_command = "declare-var" if isSynthesis else "declare-const"
        out.write(
            "\n%s\n\n"
            % "\n".join(
                [
                    "(%s %s %s)" % (var_decl_command, v[0], v[1].toSMT())
                    for v in declarations
                ]
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
            out.write("%s\n\n" % Constraint(vc).toSMT())
            out.write("(check-synth)")
        else:
            out.write("%s\n\n" % MLInst_Assert(Not(vc).toSMT()))
            out.write("(check-sat)\n(get-model)")
