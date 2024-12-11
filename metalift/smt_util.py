import importlib.resources as resources
import typing
from typing import Any, Union, get_args

import networkx as nx

from metalift import utils
from metalift.ir import *


def get_direct_calls(
    target_lang: list[FnDecl | FnDeclRecursive],
) -> dict[str, set[str]]:
    """Returns a mapping from function names to a set of function names that call them."""

    def get_fn_direct_calls(
        expr: Expr | Any, fn_call: str, direct_calls: dict[str, set[str]]
    ) -> Expr:
        if not isinstance(expr, Expr):
            return expr
        if isinstance(expr, Call):
            if expr.name() != fn_call:
                if expr.name() not in direct_calls:
                    direct_calls[expr.name()] = set()
                direct_calls[expr.name()].add(fn_call)
        return expr.map_args(
            lambda expr: get_fn_direct_calls(expr, fn_call, direct_calls)
        )

    direct_calls: dict[str, set[str]] = {}
    for fn_decl in target_lang:
        fn_decl.map_args(
            lambda expr: get_fn_direct_calls(expr, fn_decl.name(), direct_calls)
        )
    return direct_calls


def get_direct_in_calls(
    fn_decls: list[FnDecl | FnDeclRecursive],
    in_calls: list[tuple[str, str]],
) -> list[tuple[str, str]]:
    """Sometimes, only indirect in calls are provided. For example, matrix selection two args takes in select_two_args_arg argument, and it is used in selection_two_args as well.

    At the time of this function being invoked, in_calls should only have
    (matrix_selection_two_args, select_two_args_arg), but we want in_calls to have (selection_two_args, select_two_args_arg) as well.
    """

    def get_fn_direct_in_calls(
        *,
        expr: Expr | Any,
        fn_call: str,
        in_call: str,
        direct_in_calls: list[tuple[str, str]],
    ) -> Expr:
        if not isinstance(expr, Expr):
            return expr
        if isinstance(expr, Call):
            if any(is_fn_decl_type(arg.type) for arg in expr.arguments()):
                # Then this is a higher order function
                fn_call = expr.name()
            for arg in expr.arguments():
                arg.map_args(
                    lambda arg: get_fn_direct_in_calls(
                        expr=arg,
                        fn_call=expr.name(),
                        in_call=in_call,
                        direct_in_calls=direct_in_calls,
                    )
                )
        elif isinstance(expr, CallValue):
            direct_in_calls.append((fn_call, in_call))
        return expr.map_args(
            lambda expr: get_fn_direct_in_calls(
                expr=expr,
                fn_call=fn_call,
                in_call=in_call,
                direct_in_calls=direct_in_calls,
            )
        )

    fn_name_to_in_calls: dict[str, set[str]] = {}
    for fn_name, in_call in in_calls:
        if fn_name not in fn_name_to_in_calls:
            fn_name_to_in_calls[fn_name] = set()
        fn_name_to_in_calls[fn_name].add(in_call)

    direct_in_calls: list[tuple[str, str]] = []
    for fn_decl in fn_decls:
        relevant_in_calls = fn_name_to_in_calls.get(fn_decl.name(), set())
        for in_call in relevant_in_calls:
            fn_decl.map_args(
                lambda expr: get_fn_direct_in_calls(
                    expr=expr,
                    fn_call=fn_decl.name(),
                    in_call=in_call,
                    direct_in_calls=direct_in_calls,
                )
            )
    return direct_in_calls


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


def filter_args(argList: typing.List[Expr]) -> typing.List[Expr]:
    newArgs = []
    for a in argList:
        if not is_fn_decl_type(a.type):
            newArgs.append(a)
    return newArgs


def filter_fn_args(expr: Expr) -> Expr:
    if (not isinstance(expr, Expr)) or isinstance(expr, Var) or isinstance(expr, Lit):
        return expr
    if isinstance(expr, Call):
        new_args = []
        for arg in expr.arguments():
            if not is_fn_decl_type(arg.type):
                new_args.append(filter_fn_args(arg))
        return Call(expr.name(), expr.type, *new_args)
    else:
        return expr.map_args(lambda x: filter_fn_args(x))


def replace_fn_name(
    *,
    expr: Expr,
    new_fn_name: str,
    fn_name: str,
) -> Expr:
    if (not isinstance(expr, Expr)) or isinstance(expr, Var) or isinstance(expr, Lit):
        return expr
    if isinstance(expr, Call):
        new_args = []
        final_fn_name = expr.name()
        for arg in expr.arguments():
            new_args.append(
                replace_fn_name(expr=arg, new_fn_name=new_fn_name, fn_name=fn_name)
            )
        if expr.name() == fn_name:
            final_fn_name = new_fn_name
        return Call(final_fn_name, expr.type, *new_args)
    else:
        return expr.map_args(
            lambda x: replace_fn_name(expr=x, new_fn_name=new_fn_name, fn_name=fn_name)
        )


def augment_arguments(
    *, expr: Expr, fn_name: str, new_args: list[Expr], start_index: int
) -> Expr:
    if (not isinstance(expr, Expr)) or isinstance(expr, Var) or isinstance(expr, Lit):
        return expr
    if isinstance(expr, Call):
        processed_args: list[Expr] = []
        for arg in expr.arguments():
            processed_args.append(
                augment_arguments(
                    expr=arg,
                    fn_name=fn_name,
                    new_args=new_args,
                    start_index=start_index,
                )
            )
        if expr.name() == fn_name:
            return Call(
                fn_name,
                expr.type,
                *processed_args[:start_index],
                *new_args,
                *processed_args[start_index:],
            )
        else:
            return Call(expr.name(), expr.type, *processed_args)
    else:
        return expr.map_args(
            lambda x: augment_arguments(
                expr=x, fn_name=fn_name, new_args=new_args, start_index=start_index
            )
        )


def replace_fn_name_with_in_call(
    *, expr: Expr, new_fn_name: str, fn_name: str, in_call: str
) -> Expr:
    if (not isinstance(expr, Expr)) or isinstance(expr, Var) or isinstance(expr, Lit):
        return expr
    if isinstance(expr, Call):
        final_fn_name = expr.name()
        if expr.name() == fn_name and any(
            is_fn_decl_type(arg.type) and arg.name() == in_call
            for arg in expr.arguments()
        ):
            final_fn_name = new_fn_name
        return Call(
            final_fn_name,
            expr.type,
            *[
                replace_fn_name_with_in_call(
                    expr=arg, new_fn_name=new_fn_name, fn_name=fn_name, in_call=in_call
                )
                for arg in expr.arguments()
            ],
        )
    else:
        return expr.map_args(
            lambda x: replace_fn_name_with_in_call(
                expr=x, new_fn_name=new_fn_name, fn_name=fn_name, in_call=in_call
            )
        )


def filter_body(
    *, fun_def: Expr, new_fn_call: str, fn_call: str, in_call: Optional[str] = None
) -> Expr:
    if (
        (not isinstance(fun_def, Expr))
        or isinstance(fun_def, Var)
        or isinstance(fun_def, Lit)
    ):
        return fun_def
    if isinstance(fun_def, Call):
        new_args = []
        for arg in fun_def.arguments():
            if not is_fn_decl_type(arg.type):
                new_args.append(
                    filter_body(
                        fun_def=arg,
                        new_fn_call=new_fn_call,
                        fn_call=fn_call,
                        in_call=in_call,
                    )
                )
        fn_name = fun_def.name()
        if fn_call == fn_name:
            fn_name = new_fn_call
        return Call(fn_name, fun_def.type, *new_args)
    elif isinstance(fun_def, CallValue):
        new_args = []
        for arg in fun_def.arguments():
            new_args.append(
                filter_body(
                    fun_def=arg,
                    new_fn_call=new_fn_call,
                    fn_call=fn_call,
                    in_call=in_call,
                )
            )
        if in_call is None:
            raise Exception("in call is None!")
        return Call(in_call, fun_def.type, *new_args)
    else:
        return fun_def.map_args(
            lambda x: filter_body(
                fun_def=x, new_fn_call=new_fn_call, fn_call=fn_call, in_call=in_call
            )
        )


def toSMT(
    target_lang: list[FnDecl | FnDeclRecursive | Axiom],
    vars: set[Var],
    inv_and_ps: typing.Sequence[Union[FnDeclRecursive, Synth]],
    preds: Union[str, typing.List[Any]],
    vc: Expr,
    out_file: str,
    in_calls: list[tuple[str, str]],
    fn_calls: list[str],
    is_synthesis: bool = False,
) -> None:
    # order of appearance: inv and ps grammars, vars, non inv and ps preds, vc
    with open(out_file, mode="w") as out:
        out.write(resources.read_text(utils, "tuples.smt"))
        if not is_synthesis:
            out.write(resources.read_text(utils, "integer-fn-axioms.smt"))
            out.write(resources.read_text(utils, "list-axioms.smt"))
            # out.write(resources.read_text(utils, "map-axioms.smt"))

        early_candidates_names = set()

        fn_decls: list[FnDecl | FnDeclRecursive] = []
        axioms: list[Axiom] = []
        target_lang = topological_sort(target_lang)

        direct_calls = get_direct_calls(
            [fn_decl for fn_decl in target_lang if not isinstance(fn_decl, Axiom)]
        )
        direct_in_calls = get_direct_in_calls(
            fn_decls=[
                fn_decl for fn_decl in target_lang if not isinstance(fn_decl, Axiom)
            ],
            in_calls=in_calls,
        )

        rewritten_fn_decls: set[Expr] = set()
        in_calls_to_renamed_fn_name: dict[tuple[str, str], str] = {}

        # First, we want to replace all the direct in calls.
        for t in target_lang:
            if (
                isinstance(t, FnDeclRecursive) or isinstance(t, FnDecl)
            ) and t.name() in fn_calls:
                for i in direct_in_calls:
                    if i[0] == t.name():
                        rewritten_fn_decls.add(t)
                        early_candidates_names.add(i[1])
                        # If we are doing the first round, then it means we are rewritting
                        # functions that have direct calls to the inlined function. An example
                        # of such a function is selection_two_args.
                        new_fn_name = f"{t.name()}_{i[1]}"
                        new_body = filter_body(
                            fun_def=t.body(),
                            new_fn_call=new_fn_name,
                            fn_call=i[0],
                            in_call=i[1],
                        )
                        # remove function type args
                        new_args = filter_args(t.arguments())

                        in_calls_to_renamed_fn_name[(t.name(), i[1])] = new_fn_name
                        fn_decls.append(
                            FnDeclRecursive(
                                new_fn_name,
                                t.returnT(),
                                new_body,
                                *new_args,
                            )
                            if isinstance(t, FnDeclRecursive)
                            else FnDecl(
                                new_fn_name,
                                t.returnT(),
                                new_body,
                                *new_args,
                            )
                        )

        # Now, we start iteratively replacing function calls with the inlined-function-rewritten versions.
        while len(in_calls_to_renamed_fn_name) > 0:
            # We need to rename all such functions in the synthesized ones.
            for idx, cand in enumerate(inv_and_ps):
                for (
                    fn_name,
                    in_call,
                ), new_fn_name in in_calls_to_renamed_fn_name.items():
                    new_body = replace_fn_name_with_in_call(
                        expr=cand.body(),
                        new_fn_name=new_fn_name,
                        fn_name=fn_name,
                        in_call=in_call,
                    )
                    cand.set_body(new_body)
                inv_and_ps[idx] = cand

            new_in_calls_to_renamed_fn_name: dict[tuple[str, str], str] = {}
            for idx, t in enumerate(target_lang):
                if isinstance(t, Axiom):
                    axiom = t
                    for (
                        fn_name,
                        in_call,
                    ), new_fn_name in in_calls_to_renamed_fn_name.items():
                        axiom = replace_fn_name(
                            expr=axiom, new_fn_name=new_fn_name, fn_name=fn_name
                        )
                        axiom = filter_fn_args(axiom)
                    target_lang[idx] = axiom

            for (fn_name, in_call), new_fn_name in in_calls_to_renamed_fn_name.items():
                fn_callers = direct_calls.get(fn_name, set())
                for t in target_lang:
                    if isinstance(t, Axiom):
                        continue
                    if t.name() not in fn_callers:
                        continue
                    new_body = filter_body(
                        fun_def=t.body(),
                        new_fn_call=new_fn_name,
                        fn_call=fn_name,
                        in_call=None,
                    )

                    new_fn_name = f"{t.name()}_{new_fn_name}"
                    new_body = filter_body(
                        fun_def=new_body,
                        new_fn_call=new_fn_name,
                        fn_call=t.name(),
                        in_call=None,
                    )
                    new_args = filter_args(t.arguments())

                    new_in_calls_to_renamed_fn_name[(t.name(), in_call)] = new_fn_name
                    rewritten_fn_decls.add(t)
                    fn_decls.append(
                        FnDeclRecursive(
                            new_fn_name,
                            t.returnT(),
                            new_body,
                            *new_args,
                        )
                        if isinstance(t, FnDeclRecursive)
                        else FnDecl(
                            new_fn_name,
                            t.returnT(),
                            new_body,
                            *new_args,
                        )
                    )
            in_calls_to_renamed_fn_name = new_in_calls_to_renamed_fn_name

        for t in target_lang:
            if t in rewritten_fn_decls:
                continue
            elif isinstance(t, Axiom):
                axioms.append(t)
            else:
                out.write("\n" + t.toSMT() + "\n")

        vc = filter_fn_args(vc)

        early_candidates: list[FnDeclRecursive | Synth] = []
        candidates: list[FnDeclRecursive | Synth] = []
        for cand in inv_and_ps:
            cand = filter_fn_args(cand)
            if cand.name() in early_candidates_names:
                early_candidates.append(cand)
            else:
                candidates.append(cand)

        candidates = topological_sort(candidates)
        out.write("\n\n".join(["\n%s\n" % cand.toSMT() for cand in early_candidates]))
        out.write("\n\n".join(["\n%s\n" % inlined.toSMT() for inlined in fn_decls]))
        out.write("\n\n".join(["\n%s\n" % axiom.toSMT() for axiom in axioms]))
        out.write("\n\n".join(["\n%s\n" % cand.toSMT() for cand in candidates]))

        declarations: typing.List[tuple[str, ObjectT]] = []
        for v in vars:
            declarations.append((v.args[0], v.type))

        var_decl_command = "declare-var" if is_synthesis else "declare-const"
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

        if is_synthesis:
            out.write("%s\n\n" % Constraint(vc).toSMT())
            out.write("(check-synth)")
        else:
            out.write("%s\n\n" % MLInst_Assert(Not(vc).toSMT()))
            out.write("(check-sat)\n(get-model)")
