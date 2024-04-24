import re
from typing import Dict

from llvmlite.binding import ValueRef

from metalift.frontend.utils import ObjectSet
from metalift.ir import And, Bool, Expr, Int, Lit, Or, get_object_exprs


def parse_operand(op: ValueRef, reg: Dict[str, Expr], hasType: bool = True) -> Expr:
    # op is a ValueRef, and if it has a name then it's a register
    if op.name:  # a reg
        try:
            return reg[op.name]
        except KeyError:
            # hack due to ValueRef only using referential equality
            for regKey in reg.keys():
                if str(regKey) == str(op):
                    return reg[regKey]
            raise KeyError("")
    elif hasType:  # i32 0
        val = re.search("\w+ (\S+)", str(op)).group(1)  # type: ignore
        if val == "true":
            return Lit(True, Bool)
        elif val == "false":
            return Lit(False, Bool)
        else:  # assuming it's a number
            return Lit(int(val), Int)
    else:  # 0
        return Lit(int(op), Int)


def and_exprs(*exprs: Expr) -> Expr:
    if len(exprs) == 0:
        raise Exception("Must provide at least one expression!")
    result = exprs[0]
    for expr in exprs[1:]:
        result = And(result, expr)
    return result


# TODO: should this belong to the same function as and_exprs or different?
def or_exprs(*exprs: Expr) -> Expr:
    if len(exprs) == 0:
        raise Exception("Must provide at least one expression!")
    result = exprs[0]
    for expr in exprs[1:]:
        result = Or(result, expr)
    return result


def and_objects(*objects: Bool) -> Bool:
    deduped_objects = ObjectSet(objects).objects()
    return Bool(and_exprs(*get_object_exprs(*deduped_objects)))


def or_objects(*objects: Bool) -> Bool:
    deduped_objects = ObjectSet(objects).objects()
    return Bool(or_exprs(*get_object_exprs(*deduped_objects)))
