from enum import Enum

from llvmlite.binding import ValueRef


class Expr:
  class Kind(Enum):
    Var = "var"
    Lit = "lit"

    Add = "+"
    Sub = "-"

    Eq = "="
    Lt = "<"
    Le = "<="

    And = "and"
    Or = "or"
    Not = "not"

    Implies = "=>"

    Ite = "ite"

    Pred = "pred"

    Assert = "assert"

  class Type(Enum):
    Bool = "Bool"
    Int = "Int"

    def __str__(self):
      return self.value


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
  def Add(*args): return Expr(Expr.Kind.Add, Expr.Type.Int, args)
  @staticmethod
  def Sub(*args): return Expr(Expr.Kind.Sub, Expr.Type.Int, args)

  @staticmethod
  def Eq(e1, e2): return Expr(Expr.Kind.Eq, Expr.Type.Bool, [e1, e2])
  @staticmethod
  def Lt(e1, e2): return Expr(Expr.Kind.Lt, Expr.Type.Bool, [e1, e2])
  @staticmethod
  def Le(e1, e2): return Expr(Expr.Kind.Le, Expr.Type.Bool, [e1, e2])

  @staticmethod
  def And(*args): return Expr(Expr.Kind.And, Expr.Type.Bool, args)
  @staticmethod
  def Or(*args): return Expr(Expr.Kind.Or, Expr.Type.Bool, args)
  @staticmethod
  def Not(e): return Expr(Expr.Kind.Not, Expr.Type.Bool, [e])

  @staticmethod
  def Implies(e1, e2): return Expr(Expr.Kind.Implies, Expr.Type.Bool, [e1, e2])

  @staticmethod
  def Ite(c, e1, e2): return Expr(Expr.Kind.Ite, e1.type, [c, e1, e2])

  @staticmethod
  def Pred(name, returnT, *args): return Expr(Expr.Kind.Pred, returnT, [name, *args])

  @staticmethod
  def Assert(e): return Expr(Expr.Kind.Assert, Expr.Type.Bool, [e])


# class to represent extra instructions inserted into the input code
# as a result of code transformations before VC computation
class MLInstruction:
  def __init__(self, opcode, *operands):
    self.opcode = opcode
    self.operands = operands

  def __str__(self):
    if self.opcode == "load":
      return "(load %s)" % " ".join([o.name if isinstance(o, ValueRef) else str(o) for o in self.operands])
    else: return "  %s %s" % (self.opcode, " ".join([o.name if isinstance(o, ValueRef) else str(o)
                                              for o in self.operands]))

class MLValueRef:
  def __init__(self, name, ty):
    self.name = name
    self.ty = ty

  def __str__(self):
    return self.name
