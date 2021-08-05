from enum import Enum

from llvmlite.binding import ValueRef, TypeRef


class Type: #(Enum):
  #Bool = "Bool"
  #Int = "Int"


  def __init__(self, name, *args):
    self.name = name
    self.args = args

  @staticmethod
  def int(): return Type("Int", [])
  @staticmethod
  def bool(): return Type("Bool", [])
  @staticmethod
  def pointer(): return Type("Pointer", [])
  @staticmethod
  def list(contentT): return Type("MLList", [contentT])

  def __repr__(self):
    #return self.value
    if self.name == "Int": return "Int"
    elif self.name == "Bool": return "Bool"
    else: return "(%s %s)" % (self.name, " ".join([str(a) for a in self.args]))


class Expr:
  class Kind(Enum):
    Var = "var"
    Lit = "lit"

    Add = "+"
    Sub = "-"

    Eq = "="
    Lt = "<"
    Le = "<="
    Gt = ">"
    Ge = ">="

    And = "and"
    Or = "or"
    Not = "not"

    Implies = "=>"

    Ite = "ite"

    Pred = "pred"

    Assert = "assert"
    Constraint = "constraint"
    Synth = "synth"
    Choose = "choose"


  def __init__(self, kind, type, args):
    self.kind = kind
    self.args = args
    self.type = type

  def __repr__(self):
    kind = self.kind
    if kind == Expr.Kind.Var or kind == Expr.Kind.Lit:
      return str(self.args[0])
    elif kind == Expr.Kind.Pred:
      return "(" + " ".join([a.name if isinstance(a, ValueRef) and a.name != "" else str(a) for a in self.args]) + ")"
    else:
      return "(" + self.kind.value + " " + " ".join([a.name if isinstance(a, ValueRef) and a.name != "" else str(a)
                                                     for a in self.args]) + ")"

  def __eq__(self, other):
    if isinstance(other, Expr):
      if self.kind != other.kind or len(self.args) != len(other.args):
        return False
      else:
        return all( a1 == a2 if isinstance(a1, type) and isinstance(a2, type) else a1.__eq__(a2)
                    for a1,a2 in zip(self.args, other.args))
    return NotImplemented

  def __ne__(self, other):
    x = self.__eq__(other)
    if x is not NotImplemented:
      return not x
    return NotImplemented

  def __hash__(self):
    return hash(tuple(sorted({'kind': self.kind, 'type': self.type, 'args': tuple(self.args)})))


  @staticmethod
  def Var(name, ty): return Expr(Expr.Kind.Var, ty, [name])
  @staticmethod
  def Lit(val, ty): return Expr(Expr.Kind.Lit, ty, [val])

  @staticmethod
  def Add(*args): return Expr(Expr.Kind.Add, Type.int(), args)
  @staticmethod
  def Sub(*args): return Expr(Expr.Kind.Sub, Type.int(), args)

  @staticmethod
  def Eq(e1, e2): return Expr(Expr.Kind.Eq, Type.bool(), [e1, e2])
  @staticmethod
  def Lt(e1, e2): return Expr(Expr.Kind.Lt, Type.bool(), [e1, e2])
  @staticmethod
  def Le(e1, e2): return Expr(Expr.Kind.Le, Type.bool(), [e1, e2])
  @staticmethod
  def Gt(e1, e2): return Expr(Expr.Kind.Gt, Type.bool(), [e1, e2])
  @staticmethod
  def Ge(e1, e2): return Expr(Expr.Kind.Ge, Type.bool(), [e1, e2])


  @staticmethod
  def And(*args): return Expr(Expr.Kind.And, Type.bool(), args)
  @staticmethod
  def Or(*args): return Expr(Expr.Kind.Or, Type.bool(), args)
  @staticmethod
  def Not(e): return Expr(Expr.Kind.Not, Type.bool(), [e])

  @staticmethod
  def Implies(e1, e2): return Expr(Expr.Kind.Implies, Type.bool(), [e1, e2])

  @staticmethod
  def Ite(c, e1, e2): return Expr(Expr.Kind.Ite, e1.type, [c, e1, e2])

  @staticmethod
  def Pred(name, returnT, *args): return Expr(Expr.Kind.Pred, returnT, [name, *args])
  @staticmethod
  def Assert(e): return Expr(Expr.Kind.Assert, Type.bool(), [e])
  @staticmethod
  def Constraint(e): return Expr(Expr.Kind.Constraint, Type.bool(), [e])
  @staticmethod
  def Choose(*args): return Expr(Expr.Kind.Choose, args[0].type, args)
  # the body of a synth-fun
  @staticmethod
  def Synth(name, body, *args): return Expr(Expr.Kind.Synth, body.type, [name, body, *args])


# class to represent the extra instructions that are inserted into the llvm code during analysis
class MLInst:
  class Kind:  # not defined as an enum as computeVC switches on the opcode str
    Assert = "assert"
    Assume = "assume"
    Call = "call"
    Eq = "eq"
    Havoc = "havoc"
    Load = "load"
    Not = "not"
    Or = "or"
    Return = "return"

  def __init__(self, opcode, *operands):
    self.opcode = opcode
    self.operands = operands

  def __str__(self):
    if self.opcode == "call":
      return "call %s %s(%s)" % (self.operands[0], self.operands[1], " ".join([o.name if isinstance(o, ValueRef) else str(o)
                                                                          for o in self.operands[2:]]))
    else:
      return "(%s %s)" % (self.opcode, " ".join([o.name if isinstance(o, ValueRef) else str(o)
                                              for o in self.operands]))

  @staticmethod
  def Assert(val): return MLInst(MLInst.Kind.Assert, val)
  @staticmethod
  def Assume(val): return MLInst(MLInst.Kind.Assume, val)
  @staticmethod
  def Call(name, retType, *args): return MLInst(MLInst.Kind.Call, name, retType, *args)
  @staticmethod
  def Eq(v1, v2): return MLInst(MLInst.Kind.Eq, v1, v2)
  @staticmethod
  def Havoc(*args): return MLInst(MLInst.Kind.Havoc, *args)
  @staticmethod
  def Load(val): return MLInst(MLInst.Kind.Load, val)
  @staticmethod
  def Not(val): return MLInst(MLInst.Kind.Not, val)
  @staticmethod
  def Or(val): return MLInst(MLInst.Kind.Or, val)
  @staticmethod
  def Return(val): return MLInst(MLInst.Kind.Return, val)


class MLValueRef:
  def __init__(self, name, ty):
    self.name = name
    self.ty = ty

  def __str__(self):
    return self.name


def parseTypeRef(t: TypeRef):
  # ty.name returns empty string. possibly bug
  tyStr = str(t)
  if tyStr == "i64": return Type.int()
  elif tyStr == "i32" or tyStr == "i32*" : return Type.int()
  elif tyStr == "i1": return Type.bool()
  elif tyStr == "%struct.list*": return Type("MLList", Type.int())

  else: raise Exception("NYI %s" % t)
