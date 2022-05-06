# utils for converting rosette output to IR
import pyparsing as pp

import typing
from typing import Any, Callable, Dict

from metalift.ir import *


def generateAST(expr: str) -> typing.List[Any]:
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
    varType: Dict[str, Type],
    choices: Dict[str, Expr],
    typeHint: typing.Optional[Type] = None,
) -> Expr:

    expr_bi: Dict[str, Callable[..., Expr]] = {
        "equal?": Eq,
        "+": Add,
        "-": Sub,
        "*": Mul,
        "<": Lt,
        "<=": Le,
        ">": Gt,
        ">=": Ge,
        "&&": And,
        "or": Or,
        "=>": Implies,
    }
    expr_uni = {"not": Not}
    if isinstance(ast, list):
        if ast[0] == "define":
            return toExpr(ast[2], fnsType, varType, choices)
        elif ast[0] == "choose":
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
        elif ast[0] == "length":
            return Call("list_length", Int(), toExpr(ast[1], fnsType, varType, choices))
        elif ast[0] == "=":
            return Eq(
                toExpr(ast[1], fnsType, varType, choices),
                toExpr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "list-empty":
            return Call("list_empty", List(Int()))
        elif ast[0] == "list-append" or ast[0] == "append":
            elem = toExpr(ast[2], fnsType, varType, choices)
            return Call(
                "list_append",
                List(elem.type),
                toExpr(ast[1], fnsType, varType, choices),
                elem,
            )
        elif ast[0] == "list-prepend":
            elem = toExpr(ast[1], fnsType, varType, choices)
            return Call(
                "list_prepend",
                List(elem.type),
                elem,
                toExpr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "list-ref-noerr":
            list_expr = toExpr(ast[1], fnsType, varType, choices)
            return Call(
                "list_get",
                list_expr.type.args[0],
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
        elif ast[0] == "list-concat":
            return Call(
                "list_concat",
                List(Int()),
                toExpr(ast[1], fnsType, varType, choices),
                toExpr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "list-take-noerr":
            return Call(
                "list_take",
                List(Int()),
                toExpr(ast[1], fnsType, varType, choices),
                toExpr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "make-tuple":
            arg_eval = []
            for alen in range(1, len(ast)):
                arg_eval.append(toExpr(ast[alen], fnsType, varType, choices))
            return MakeTuple(*arg_eval)
        elif ast[0] == "tupleGet":
            return TupleGet(
                toExpr(ast[1], fnsType, varType, choices),
                toExpr(ast[2], fnsType, varType, choices),
            )
        elif ast[0] == "set-create":
            return Call(ast[0], Set(Int()))
        elif ast[0] == "set-insert":
            v = toExpr(ast[1], fnsType, varType, choices)
            s1 = toExpr(ast[2], fnsType, varType, choices)
            return Call(ast[0], Set(v.type), v, s1)
        elif ast[0] == "set-singleton":
            v = toExpr(ast[1], fnsType, varType, choices)
            return Call(ast[0], Set(v.type), v)
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
            return Call(ast[0], Bool(), s1, s2)
        elif ast[0] == "set-member":
            v = toExpr(ast[1], fnsType, varType, choices)
            s = toExpr(ast[2], fnsType, varType, choices)
            return Call(ast[0], Bool(), v, s)
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
                typeHint=Fn(m1.type.args[1], m1.type.args[1], m1.type.args[1]),
            )

            return Call(ast[0], m1.type, m1, m2, uf)
        elif ast[0] == "map-values":
            m = toExpr(ast[1], fnsType, varType, choices)
            return Call(ast[0], List(m.type.args[1]), m)
        elif ast[0] == "map-singleton":
            k = toExpr(ast[1], fnsType, varType, choices)
            v = toExpr(ast[2], fnsType, varType, choices)
            return Call(ast[0], Map(k.type, v.type), k, v)
        elif ast[0] == "map-create":
            return Call(ast[0], Map(None, None))  # type: ignore
        elif ast[0] == "map-get":
            m = toExpr(ast[1], fnsType, varType, choices)
            k = toExpr(ast[2], fnsType, varType, choices)
            default = toExpr(ast[3], fnsType, varType, choices)
            return Call(ast[0], m.type.args[1], m, k, default)
        elif ast[0] == "lambda":
            arg_list = [
                Var(n, t) for (t, n) in zip(typeHint.args[1:], ast[1])  # type: ignore
            ]

            varTypeUpdated = dict(varType)
            for a in arg_list:
                varTypeUpdated[a.args[0]] = a.type

            body = toExpr(ast[2], fnsType, varTypeUpdated, choices)
            return Lambda(body.type, body, *arg_list)
        elif ast[0] == "let":
            var_value = toExpr(ast[1][0][1], fnsType, varType, choices)
            tmp_var_type = dict(varType)
            tmp_var_type[ast[1][0][0]] = var_value.type
            return Let(
                Var(ast[1][0][0], var_value.type),
                var_value,
                toExpr(ast[2], fnsType, tmp_var_type, choices),
            )
        elif ast[0] in fnsType.keys():
            arg_eval = []
            for alen in range(1, len(ast)):
                arg_eval.append(
                    toExpr(
                        ast[alen],
                        fnsType,
                        varType,
                        choices,
                        typeHint=fnsType[ast[0]].args[alen],
                    )
                )
            retT = fnsType[ast[0]].args[0]
            return Call(ast[0], retT, *arg_eval)
        elif ast[0] in choices:
            picked: Expr = choices[ast[0]].args[0]
            while (
                picked.kind == Expr.Kind.Var
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
