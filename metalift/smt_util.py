import importlib.resources as resources
import typing
from typing import Any, Union, get_args

import networkx as nx

from metalift import utils
from metalift.ir import *


def get_dependent_fn_names(
    expr: Any, all_fn_names: List[str], dependent_fn_names: List[str]
) -> None:
    if isinstance(expr, str) and expr in all_fn_names:
        dependent_fn_names.append(expr)
        return
    elif isinstance(expr, Expr):
        for arg in expr.args:
            get_dependent_fn_names(arg, all_fn_names, dependent_fn_names)


def topological_sort(
    fn_decls_and_axioms: List[Union[FnDecl, FnDeclRecursive, Axiom]]
) -> List[Union[FnDecl, FnDeclRecursive, Axiom]]:
    # First we construct a DAG
    graph = nx.DiGraph()
    edges: List[Tuple[str, str]] = []
    axioms: List[Axiom] = []
    fn_decls: List[Union[FnDecl, FnDeclRecursive]] = []
    for f in fn_decls_and_axioms:
        if isinstance(f, FnDeclRecursive) or isinstance(f, FnDecl):
            fn_decls.append(f)
        else:
            axioms.append(f)

    all_fn_names = [fn_decl.name() for fn_decl in fn_decls]
    for fn_decl in fn_decls:
        dependent_fn_names: List[str] = []
        get_dependent_fn_names(fn_decl.body(), all_fn_names, dependent_fn_names)
        edges.extend(
            [
                (dependent_fn_name, fn_decl.name())
                for dependent_fn_name in dependent_fn_names
                if fn_decl.name() != dependent_fn_name
            ]
        )
    graph.add_edges_from(edges)
    ordered_fn_names = list(nx.topological_sort(graph))
    independent_fn_names = set(all_fn_names) - set(ordered_fn_names)

    fn_name_to_decl = {fn_decl.name(): fn_decl for fn_decl in fn_decls}
    dependent_fn_decls = [fn_name_to_decl[fn_name] for fn_name in ordered_fn_names]
    independent_fn_decls = [
        fn_name_to_decl[fn_name] for fn_name in independent_fn_names
    ]
    return dependent_fn_decls + independent_fn_decls + axioms


def filterArgs(argList: typing.List[Expr]) -> typing.List[Expr]:
    newArgs = []
    for a in argList:
        if not is_fn_decl_type(a.type):
            newArgs.append(a)
    return newArgs


def filterBody(funDef: Expr, funCall: str, inCall: str) -> Expr:
    if (
        (not isinstance(funDef, Expr))
        or isinstance(funDef, Var)
        or isinstance(funDef, Lit)
    ):
        return funDef
    if isinstance(funDef, Call):
        newArgs = []
        for i in range(1, len(funDef.args)):
            if not is_fn_decl_type(funDef.args[i].type):
                newArgs.append(filterBody(funDef.args[i], funCall, inCall))
        return Call(funDef.name(), funDef.type, *newArgs)
    elif isinstance(funDef, CallValue):
        newArgs = []

        for i in range(1, len(funDef.args)):
            newArgs.append(filterBody(funDef.args[i], funCall, inCall))
        return Call(inCall, funDef.type, *newArgs)
    else:
        return funDef.map_args(lambda x: filterBody(x, funCall, inCall))


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
            out.write(resources.read_text(utils, "integer-fn-axioms.smt"))
            out.write(resources.read_text(utils, "list-axioms.smt"))
            out.write(resources.read_text(utils, "map-axioms.smt"))

        early_candidates_names = set()
        synthesized_fn_names = set(fn.name() for fn in invAndPs)

        fn_decls = []
        axioms = []
        targetLang = topological_sort(targetLang)
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
                        fn_decls.append(
                            FnDeclRecursive(
                                t.name(),  # TODO(jie): this only handles single function param
                                # t.args[0] + "_" + i[1],
                                t.returnT(),
                                newBody,
                                *newArgs,
                            )
                            # if t.kind == Expr.Kind.FnDecl
                            if isinstance(t, FnDeclRecursive)
                            else FnDecl(
                                t.name(),  # TODO(jie): this only handles single function param
                                # t.args[0] + "_" + i[1],
                                t.returnT(),
                                newBody,
                                *newArgs,
                            )
                        )
                if not found_inline and t.name() not in synthesized_fn_names:
                    out.write("\n" + t.toSMT() + "\n")

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
                    # TODO: cand.type no longer has args, find proper substitution
                    cand.args[0],
                    get_fn_return_type(cand.type),
                    newBody,
                    *cand.args[2:],
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

        candidates = topological_sort(candidates)
        out.write("\n\n".join(["\n%s\n" % cand.toSMT() for cand in early_candidates]))
        out.write("\n\n".join(["\n%s\n" % inlined.toSMT() for inlined in fn_decls]))
        out.write("\n\n".join(["\n%s\n" % axiom.toSMT() for axiom in filtered_axioms]))
        out.write("\n\n".join(["\n%s\n" % cand.toSMT() for cand in candidates]))

        declarations: typing.List[typing.Tuple[str, ObjectT]] = []
        for v in vars:
            declarations.append((v.args[0], v.type))

        var_decl_command = "declare-var" if isSynthesis else "declare-const"
        out.write(
            "\n%s\n\n"
            % "\n".join(
                [
                    "(%s %s %s)"
                    % (var_decl_command, v[0], v[1].toSMTType(get_args(v[1])))  # type: ignore
                    for v in declarations
                ]
            )
        )

        ##### TODO: write axioms using the construct
        # if "count" in outFile:
        #     out.write(open("./utils/map_reduce_axioms.txt", "r").read())

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
