import re

from llvmlite.binding import ValueRef
from metalift.ir import And, Expr, Lit, Bool, Int, Or
from typing import Dict


def parseOperand(op: ValueRef, reg: Dict[ValueRef, Expr], hasType: bool = True) -> Expr:
    # op is a ValueRef, and if it has a name then it's a register
    if op.name:  # a reg
        try:
            return reg[op]
        except KeyError:
            # hack due to ValueRef only using referential equality
            for regKey in reg.keys():
                if str(regKey) == str(op):
                    return reg[regKey]
            raise KeyError("")
    elif hasType:  # i32 0
        val = re.search("\w+ (\S+)", str(op)).group(1)  # type: ignore
        if val == "true":
            return Lit(True, Bool())
        elif val == "false":
            return Lit(False, Bool())
        else:  # assuming it's a number
            return Lit(int(val), Int())
    else:  # 0
        return Lit(int(op), Int())


def and_exprs(*exprs: Expr) -> Expr:
    if len(exprs) == 1:
        return exprs[0]
    else:
        return And(*exprs)


# TODO: should this belong to the same function as and_exprs or different?
def or_exprs(*exprs: Expr) -> Expr:
    if len(exprs) == 1:
        return exprs[0]
    else:
        return Or(*exprs)
