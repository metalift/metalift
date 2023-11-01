import re

from llvmlite.binding import ValueRef
from metalift.ir import And, Expr, Lit, BoolObject, IntObject, Or, get_object_exprs
from typing import Dict


def parseOperand(op: ValueRef, reg: Dict[str, Expr], hasType: bool = True) -> Expr:
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
            return Lit(True, BoolObject)
        elif val == "false":
            return Lit(False, BoolObject)
        else:  # assuming it's a number
            return Lit(int(val), IntObject)
    else:  # 0
        return Lit(int(op), IntObject)


def and_exprs(*exprs: Expr) -> Expr:
    if len(exprs) == 1:
        return exprs[0]
    else:
        return And(*exprs)


def and_objects(*objects: BoolObject) -> BoolObject:
    return BoolObject(and_exprs(*get_object_exprs(objects)))


# TODO: should this belong to the same function as and_exprs or different?
def or_exprs(*exprs: Expr) -> Expr:
    if len(exprs) == 1:
        return exprs[0]
    else:
        return Or(*exprs)


def or_objects(*objects: BoolObject) -> BoolObject:
    return BoolObject(or_exprs(*get_object_exprs(objects)))
