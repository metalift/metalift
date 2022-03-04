from ir import *
from llvmlite.binding import ValueRef

import typing
from typing import Optional, Dict, Union, Any


def generateTypes(lang: typing.List[Union[Expr, ValueRef]]) -> Dict[str, Type]:
    fnsType = {}

    for l in lang:
        if l.type.name == "Function":
            if not isinstance(l, ValueRef):
                fnsType[l.args[0]] = l.type
            else:
                fnsType[l.name] = parseTypeRef(l.type)
        else:
            if not isinstance(l, ValueRef):
                fnsType[l.args[0]] = l.type
            else:
                fnsType[l.name] = parseTypeRef(l.type)
    return fnsType


def parseCandidates(
    candidate: Union[Expr, str],
    inCalls: typing.List[Any],
    fnsType: Dict[Any, Any],
    fnCalls: typing.List[Any],
) -> Optional[typing.Tuple[typing.List[Any], typing.List[Any]]]:
    if isinstance(candidate, str) or candidate.kind == Expr.Kind.Lit:
        return inCalls, fnCalls
    else:
        if candidate.kind == Expr.Kind.Call:
            if candidate.args[0] in fnsType.keys():
                fnCalls.append(candidate.args[0])
            for ar in candidate.args:
                if not isinstance(ar, str):
                    if ar.type.name == "Function":
                        # TODO(shadaj): this logic doesn't correctly handle
                        # multiple function parameters
                        inCalls.append((candidate.args[0], ar.args[0]))
        for a in candidate.args:
            parseCandidates(a, inCalls, fnsType, fnCalls)
        return inCalls, fnCalls
