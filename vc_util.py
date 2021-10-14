import re
from ir import Expr, Type, parseTypeRef, Var, Call, Lit, Bool, Int, List, Set, Eq, Lt, Le, Not, Or, And, Implies, Synth, Ite, \
  Add, Sub, BoolLit

def parseOperand(op, reg, hasType = True):
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
    val = re.search("\w+ (\S+)", str(op)).group(1)
    if val == "true": return Lit(True, Bool())
    elif val == "false": return Lit(False, Bool())
    else:  # assuming it's a number
      return Lit(int(val), Int())
  else:  # 0
    return Lit(int(op), Int())
