import re

from llvmlite.binding import ValueRef
from ir import Expr, Lit, Bool, Int
from typing import Dict


def parseOperand(op: ValueRef, reg: Dict[ValueRef, Expr], hasType: bool = True) -> Expr:
    # op is a ValueRef, and if it has a name then it's a register
    print("it is: %s" % op)
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
