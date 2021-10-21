from enum import Enum

from llvmlite.binding import ValueRef, TypeRef

class PrintMode(Enum):
  SMT = 0
  Rosette = 1
  RosetteVC = 2

printMode = PrintMode.SMT

class Type: #(Enum):
  #Bool = "Bool"
  #Int = "Int"


  def __init__(self, name, *args):
    self.name = name
    self.args = args

  def __repr__(self):
    #return self.value
    if self.name == "Int": return "Int"
    elif self.name == "Bool": return "Bool"
    else: return "(%s %s)" % (self.name, " ".join([str(a) for a in self.args]))

  def __eq__(self, other):
    if isinstance(other, Type):
      if self.name != other.name or len(self.args) != len(other.args):
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

def Int(): return Type("Int", [])
def Bool(): return Type("Bool", [])
def Pointer(): return Type("Pointer", [])
def List(contentT): return Type("MLList", contentT)
def Fn(retT, *argT): return Type("Function", retT, *argT)

class Expr:
  class Kind(Enum):
    Var = "var"
    Lit = "lit"

    Add = "+"
    Sub = "-"
    Mul = "*"

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

    Call = "call"

    Assert = "assert"
    Constraint = "constraint"
    Axiom = "axiom"
    Synth = "synth"
    Choose = "choose"
    FnDecl = "fndecl"


  def __init__(self, kind, type, args):
    self.kind = kind
    self.args = args
    self.type = type


  @staticmethod
  def findCommonExprs(e, cnts):
    if e not in cnts:
      cnts[e] = 1
      for i in range(len(e.args)):
        if isinstance(e.args[i], Expr):
          cnts = Expr.findCommonExprs(e.args[i], cnts)

    else:
      cnts[e] = cnts[e] + 1

    return cnts

  @staticmethod
  def replaceExprs(e, commonExprs, skipTop=False):
    # skipTop is used to ignore the top-level match when simplifying a common expr
    if e not in commonExprs or skipTop:
      if isinstance(e, Expr):
        newArgs = [Expr.replaceExprs(arg, commonExprs) for arg in e.args]
        if e.kind == Expr.Kind.Call:
          newArgs[0] = '_'+newArgs[0]
        return Expr(e.kind, e.type, newArgs)
      else:
        return e  # ValueRef or TypeRef
    else:
      return Var("(v%d)" % commonExprs.index(e), e.type)

  @staticmethod
  def printSynth(e):
    # commenting the code for sygus grammar generation
    # cnts = Expr.findCommonExprs(e.args[1], {})
    # commonExprs = list(filter(lambda k: cnts[k] > 1 or k.kind == Expr.Kind.Choose, cnts.keys()))
    # rewritten = Expr.replaceExprs(e.args[1], commonExprs)

    # # rewrite common exprs to use each other
    # commonExprs = [Expr.replaceExprs(e, commonExprs, skipTop=True) for e in commonExprs]

    # # (synth-fun name ( (arg type) ... ) return-type
    # # ( (return-val type) (non-term type) (non-term type) ...)
    # # ( (return-val type definition)
    # #   (non-term type definition) ... ) )
    # decls = "((rv %s) %s)" % (e.type, " ".join("(%s %s)" % ("v%d" % i, parseTypeRef(e.type)) for i, e in enumerate(commonExprs)))
    # defs = "(rv %s %s)\n" % (e.type, rewritten if rewritten.kind == Expr.Kind.Var or rewritten.kind == Expr.Kind.Lit
    #                                            else "(%s)" % rewritten)

    # defs = defs + "\n".join("(%s %s %s)" % (
    #   "v%d" % i,
    #   parseTypeRef(e.type),
    #   e if e.kind == Expr.Kind.Choose else f"({e})"
    # ) for i,e in enumerate(commonExprs))

    # body = decls + "\n" + "(" + defs + ")"

    # args = " ".join("(%s %s)" % (a.name, parseTypeRef(a.type)) for a in e.args[2:])
    # return "(synth-fun %s (%s) %s\n%s)" % (e.args[0], args, e.type, body)

    cnts = Expr.findCommonExprs(e.args[1], {})
    commonExprs = list(filter(lambda k: cnts[k] > 1 or k.kind == Expr.Kind.Choose, cnts.keys()))
    rewritten = Expr.replaceExprs(e.args[1], commonExprs)
    commonExprs = [Expr.replaceExprs(e, commonExprs, skipTop=True) for e in commonExprs]

    args = " ".join("%s" % (a.name) for a in e.args[2:])

    defs= "[rv (choose %s)]\n" % (rewritten if rewritten.kind == Expr.Kind.Var or rewritten.kind == Expr.Kind.Lit
                                               else "%s" % rewritten)

    defs =  defs + "\n".join("%s %s)]" % ("[v%d (choose" % i, e) for i,e in enumerate(commonExprs))


    return "(define-grammar (%s_gram %s)\n %s\n)" % (e.args[0], args, defs)

  def __repr__(self):
    global printMode
    listFns = {'list_get': 'list-ref-noerr','list_append': 'list-append', 'list_empty': 'list-empty', 'list_tail': 'list-tail-noerr', 'list_length': 'length'}
    kind = self.kind
    if kind == Expr.Kind.Var or kind == Expr.Kind.Lit:
      if kind == Expr.Kind.Lit and self.type == Bool():
        if self.args[0] == True:
          return "true"
        else:
          return "false"
      else:
        return str(self.args[0])
    elif kind == Expr.Kind.Call or kind == Expr.Kind.Choose:
      if isinstance(self.args[0],str):
        if (self.args[0].startswith('inv') or self.args[0].startswith('ps')) and printMode == PrintMode.RosetteVC:
          callStr = "(interpret " + "%s (vector "%(str(self.args[0]))
          for a in self.args[1:]:
            if isinstance(a, ValueRef) and a.name != "":
              callStr += "%s "%(a.name)
            else:
              if (str(a)) in listFns.keys() and 'list_empty' in (str(a)):
                callStr += '(' + listFns[str(a)] + ')' + " "
              elif (str(a)) in listFns.keys():
                 callStr += listFns[str(a)]  + " "
              else:
                callStr += str(a) + " "
          callStr += '))'
          return callStr
        elif (self.args[0].startswith('list') and printMode == PrintMode.RosetteVC):

          callStr = '(' + "%s"%(listFns[self.args[0]] if self.args[0] in listFns.keys() else self.args[0])  + " "
          for a in self.args[1:]:
            if isinstance(a, ValueRef) and a.name != "":
              callStr += "%s "%(a.name)
            else:
                callStr += str(a) + " "
          callStr += ')'
          return callStr
        else:
          if 'list_empty' in self.args:
            return   " ".join([a.name if isinstance(a, ValueRef) and a.name != "" else str(a) for a in self.args])
          else:
            return '(' + " ".join([a.name if isinstance(a, ValueRef) and a.name != "" else str(a) for a in self.args]) + ')'
      else:
        return   " ".join([a.name if isinstance(a, ValueRef) and a.name != "" else str(a) for a in self.args])
    elif kind == Expr.Kind.Synth:
      return Expr.printSynth(self)

    elif kind == Expr.Kind.Axiom:
      if printMode == PrintMode.SMT:
        vs = ["(%s %s)" % (a.args[0], a.type) for a in self.args[1:]]
        return "(assert (forall ( %s ) ) %s) " % (" ".join(vs), self.args[0])
      else: raise Exception("NYI: %s" % self)

    elif kind == Expr.Kind.FnDecl:
      if printMode == PrintMode.SMT:
        args = " ".join(["(%s %s)" % (a.name, parseTypeRef(a.type)) if isinstance(a, ValueRef) and a.name != "" else
                       "(%s %s)" % (a.args[0], parseTypeRef(a.type)) for a in self.args[2:]])

        return "(define-fun-rec %s (%s) %s\n%s)" % (self.args[0], args, self.type, self.args[1])
      else:
        args = " ".join(["%s" % (a.name) if isinstance(a, ValueRef) and a.name != "" else
                       "%s" % (a.args[0]) for a in self.args[2:]])
        return "(define-bounded (%s %s) \n%s)" % (self.args[0], args, self.args[1])
    else:
      if printMode == PrintMode.SMT: value = self.kind.value
      elif printMode == PrintMode.RosetteVC :
        k = self.kind
        if k == Expr.Kind.And: value = "&&"
        elif k == Expr.Kind.Eq: value = "equal?"
        elif k == Expr.Kind.Ite: value = "if"
        else: value = self.kind.value
      else:
        k = self.kind
        if k == Expr.Kind.And: value = "_and"
        elif k == Expr.Kind.Eq: value = "_eq"
        elif k == Expr.Kind.Or: value = "_or"
        elif k == Expr.Kind.Implies: value = "_implies"
        elif k == Expr.Kind.Not: value = "_not"
        elif k == Expr.Kind.Ite: value = "_if"
        elif k == Expr.Kind.Add: value = "_add"
        elif k == Expr.Kind.Sub: value = "_sub"
        elif k == Expr.Kind.Mul: value = "_mul"
        elif k == Expr.Kind.Le: value = "_lte"
        elif k == Expr.Kind.Lt: value = "_lt"
        elif k == Expr.Kind.Ge: value = "_gte"
        elif k == Expr.Kind.Gt: value = "_gt"

        else: value = self.kind.value

      if printMode == PrintMode.SMT or printMode == PrintMode.Rosette:
        return "(" + value + " " + " ".join([a.name if isinstance(a, ValueRef) and a.name != "" else str(a)
                                                     for a in self.args]) + ")"
      else:
        retStr = "(" + value + " "
        for a in self.args:
          if isinstance(a, ValueRef) and a.name != "":
            retStr += "%s"%(a.name) + " "
          else:
            if (str(a)) in listFns.keys() and 'list_empty' in (str(a)):
                retStr += '(' + listFns[str(a)] + ')' + " "
            elif (str(a)) in listFns.keys():
                retStr += listFns[str(a)]
            else:
                retStr += str(a) + " "
        retStr += ')'
        return retStr

  # commented out so that common exprs can be detected
  #
  # def __eq__(self, other):
  #   if isinstance(other, Expr):
  #     if self.kind != other.kind or len(self.args) != len(other.args):
  #       return False
  #     else:
  #       return all( a1 == a2 if isinstance(a1, type) and isinstance(a2, type) else a1.__eq__(a2)
  #                   for a1,a2 in zip(self.args, other.args))
  #   return NotImplemented
  #
  # def __ne__(self, other):
  #   x = self.__eq__(other)
  #   if x is not NotImplemented:
  #     return not x
  #   return NotImplemented

  def __hash__(self):
    return hash(tuple(sorted({'kind': self.kind, 'type': self.type, 'args': tuple(self.args)})))


def Var(name, ty): return Expr(Expr.Kind.Var, ty, [name])
def Lit(val, ty): return Expr(Expr.Kind.Lit, ty, [val])
def IntLit(val): return Lit(val, Int())
def BoolLit(val): return Lit(val, Bool())

def Add(*args): return Expr(Expr.Kind.Add, Int(), args)
def Sub(*args): return Expr(Expr.Kind.Sub, Int(), args)
def Mul(*args): return Expr(Expr.Kind.Mul, Int(), args)

def Eq(e1, e2): return Expr(Expr.Kind.Eq, Bool(), [e1, e2])
def Lt(e1, e2): return Expr(Expr.Kind.Lt, Bool(), [e1, e2])
def Le(e1, e2): return Expr(Expr.Kind.Le, Bool(), [e1, e2])
def Gt(e1, e2): return Expr(Expr.Kind.Gt, Bool(), [e1, e2])
def Ge(e1, e2): return Expr(Expr.Kind.Ge, Bool(), [e1, e2])

def And(*args): return Expr(Expr.Kind.And, Bool(), args)
def Or(*args): return Expr(Expr.Kind.Or, Bool(), args)
def Not(e): return Expr(Expr.Kind.Not, Bool(), [e])

def Implies(e1, e2): return Expr(Expr.Kind.Implies, Bool(), [e1, e2])

def Ite(c, e1, e2): return Expr(Expr.Kind.Ite, e1.type, [c, e1, e2])

def Call(name, returnT, *args): return Expr(Expr.Kind.Call, returnT, [name, *args])
def Assert(e): return Expr(Expr.Kind.Assert, Bool(), [e])
def Constraint(e): return Expr(Expr.Kind.Constraint, Bool(), [e])

def Axiom(e, *vars): return Expr(Expr.Kind.Axiom, Bool(), [e, *vars])

# the body of a synth-fun
def Synth(name, body, *args): return Expr(Expr.Kind.Synth, body.type, [name, body, *args])
def Choose(*args): return Expr(Expr.Kind.Choose, args[0].type, args)
def FnDecl(name, returnT, body, *args): return Expr(Expr.Kind.FnDecl, returnT, [name, body, *args])


def toRosette(targetLang, invAndPs, vars, preds, vc):
  global printMode
  printMode = PrintMode.Rosette

  #out.write("\n\n".join([str(t) for t in targetLang]))

  #out.write("\n\n%s\n\n" % invAndPs)

  varsStr = ""
  for v in vars:
    if v.type == Int(): varsStr = varsStr + "(define %s (sym-int))\n" % v.args[0]
    elif v.type == Bool(): varsStr = varsStr + "(define %s (sym-bool))\n" % v.args[0]
    elif v.type == List(Int()): varsStr = varsStr + "(define %s (sym-list 2))\n" % v.args[0]
    else: raise Exception("NYI: %s" % v)

  #vars = "\n".join(["(declare-const %s %s)" % (v.args[0], v.type) for v in vars])  # name and type

  # a list of Exprs - print name, args, return type
  predsStr = "\n".join(["(define-fun %s (%s) (%s) )" %
                     (p.args[0], " ".join("(%s %s)" % (a.args[0], a.type) for a in p.args[1:]), p.type)
                     for p in preds])

  assertions = "(define (assertions)\n (assert %s))" % vc

  return varsStr + "\n" + predsStr + "\n" + assertions



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
    if self.opcode == MLInst.Kind.Call:
      return "call %s %s(%s)" % (self.operands[0], self.operands[1], " ".join([o.name if isinstance(o, ValueRef) else str(o)
                                                                          for o in self.operands[2:]]))
    else:
      return "(%s %s)" % (self.opcode, " ".join([o.name if isinstance(o, ValueRef) else str(o)
                                              for o in self.operands]))

def MLInst_Assert(val): return MLInst(MLInst.Kind.Assert, val)
def MLInst_Assume(val): return MLInst(MLInst.Kind.Assume, val)
def MLInst_Call(name, retType, *args): return MLInst(MLInst.Kind.Call, name, retType, *args)
def MLInst_Eq(v1, v2): return MLInst(MLInst.Kind.Eq, v1, v2)
def MLInst_Havoc(*args): return MLInst(MLInst.Kind.Havoc, *args)
def MLInst_Load(val): return MLInst(MLInst.Kind.Load, val)
def MLInst_Not(val): return MLInst(MLInst.Kind.Not, val)
def MLInst_Or(val): return MLInst(MLInst.Kind.Or, val)
def MLInst_Return(val): return MLInst(MLInst.Kind.Return, val)


class MLValueRef:
  def __init__(self, name, ty):
    self.name = name
    self.ty = ty

  def __str__(self):
    return self.name


def parseTypeRef(t: TypeRef):
  # ty.name returns empty string. possibly bug
  tyStr = str(t)
  if tyStr == "i64": return Int()
  elif tyStr == "i32" or tyStr == "i32*" or tyStr == "Int": return Int()
  elif tyStr == "i1" or tyStr == "Bool": return Bool()
  elif tyStr == "%struct.list*" or tyStr == "%struct.list**"  or tyStr == "(MLList Int)": return Type("MLList", Int())

  else: raise Exception("NYI %s" % t)
