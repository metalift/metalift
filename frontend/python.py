from typing import List
from ir import Var

import operator
import inspect
import ir
import ast

class Translator(ast.NodeTransformer):
  def __init__(self):
    self.fns = {}
    self.imports = []
    self.vars = None

  # expressions
  def visit_arguments(self, n):
    # annotation here is for type, calling eval on it will return an actual type object
    #args = [ir.Var(a.arg, eval(self.visit(a.annotation))) for a in n.args]
    args = []
    for a in n.args:
      type_ = self.visit(a.annotation)
      if isinstance(type_, str):
        type_ = eval(type_)
      elif isinstance(type_, ir.ListAccess):
        type_ = eval("%s[%s]" % (type_.target, type_.index))
      else:
        raise TypeError("NYI: %s" % n)
      v = ir.Var(a.arg, type_)
      args.append(v)
      self.vars[v.name] = v

    return args

  def visit_Attribute(self, n):
    return ir.Field(self.visit(n.value), n.attr)

  def visit_BinOp(self, n):
    op = n.op
    if isinstance(op, ast.Add): new_op = operator.add
    elif isinstance(op, ast.Sub): new_op = operator.sub
    elif isinstance(op, ast.Mult): new_op = operator.mul
    elif isinstance(op, ast.Div): new_op = operator.floordiv
    else: raise TypeError("NYI; %s" % op)

    return ir.BinaryOp(new_op, self.resolve(n.left), self.resolve(n.right))

  def visit_UnaryOp(self, n):
    op = n.op
    if isinstance(op, ast.Not): new_op = operator.not_
    else: raise TypeError("NYI: %s" % op)

    return ir.UnaryOp(new_op, self.resolve(n.operand))

  def resolve(self, v, is_var=True):
    if isinstance(v, ast.Name):
      if is_var:
        if v.id not in self.vars: raise NameError("variable not found: %s" % v.id)
        else: return self.vars[v.id]
      else:  # a function
        # if v.id not in self.fns: raise NameError("function not found: %s" % v.id)
        # else: return self.fns[v.id]
        return v.id

    elif isinstance(v, ast.Attribute):  # o.f needs to resolve name XXX
      return self.visit(v)

    elif isinstance(v, ast.Num) or isinstance(v, ast.Str):
      return self.visit(v)

    elif isinstance(v, ast.Call):
      return self.visit(v)

    elif isinstance(v, ast.Constant):
      return self.visit(v)

    elif isinstance(v, ast.Subscript):
      #return self.visit(v)
      raise TypeError("xxx")

    else:
      raise TypeError("NYI: %s" % v)

  def visit_Call(self, n):
    args = [self.visit(a) for a in n.args]
    fn = self.resolve(n.func, False)

    # XXX hack for now
    if fn == "Choose" or (isinstance(fn, ir.Field) and fn.target == "ir" and fn.name == "Choose"):
      return ir.Choose(*args)
    else:
      return ir.Call(fn, *args)

  def visit_Compare(self, n):
    if len(n.ops) > 1: raise TypeError("NYI: %s" % n.ops)
    if len(n.comparators) > 1: raise TypeError("NYI: %s" % n.comparators)

    op = n.ops[0]
    if isinstance(op, ast.Eq): new_op = operator.eq
    elif isinstance(op, ast.Lt): new_op = operator.lt
    elif isinstance(op, ast.Gt): new_op = operator.gt
    elif isinstance(op, ast.LtE): new_op = operator.le
    elif isinstance(op, ast.GtE): new_op = operator.ge
    elif isinstance(op, ast.NotEq): new_op = operator.ne
    else: raise TypeError("NYI: %s" % str(op))

    return ir.BinaryOp(new_op, self.resolve(n.left), self.resolve(n.comparators[0]))

  def visit_Constant(self, n):
    t = None
    if isinstance(n.value, bool): t = bool
    elif isinstance(n.value, int): t = int  # True is also an int
    elif n.value is None: t = None
    else: raise TypeError("NYI: %s" % n.value)
    return ir.Lit(n.value, t)

  def visit_Expr(self, n):
    return self.visit(n.value)

  def visit_Index(self, n):
    return self.visit(n.value)

  def visit_Name(self, n):
    return n.id

  def visit_Starred(self, n):
    return ir.Unpack(self.visit(n.value))

  def visit_Subscript(self, n):
    return ir.ListAccess(self.visit(n.value), self.visit(n.slice), None)


  # statements
  def visit_AnnAssign(self, n):  # v:t = e
    v = ir.Var(n.target.id, eval(str(self.visit(n.annotation))))
    self.vars[v.name] = v
    val = None
    if isinstance(n.value, ast.Name):
      val = self.resolve(n.value)
    else:
      val = self.visit(n.value)
    return ir.Assign(v, val)

  def visit_Assign(self, n):
    val = None
    if isinstance(n.value, ast.Name):
      val = self.resolve(n.value)
    else:
      val = self.visit(n.value)
    if len(n.targets) > 1:
      raise TypeError("multi-assign NYI: %s" % n)
    return ir.Assign(self.vars[self.visit(n.targets[0])], val)

  def visit_FunctionDef(self, n):
    self.vars = {}
    args = self.visit(n.args)
    body = [self.visit(s) for s in n.body]
    rtype = eval(self.visit(n.returns))  # visit returns a String if n.returns is a Name
    return ir.FnDecl(n.name, args, rtype, ir.Block(*body))

  def visit_If(self, n):
    return ir.If(self.visit(n.test), ir.Block(*[self.visit(s) for s in n.body]),
                 ir.Block(*[self.visit(s) for s in n.orelse]))

  def visit_Module(self, n):
    for s in n.body:
      if isinstance(s, ast.FunctionDef):
        self.fns[s.name] = None   # placeholder
      if isinstance(s, ast.Import):
        self.imports.append(s.names[0].name)

    fns = [self.visit(f) for f in n.body if isinstance(f, ast.FunctionDef)]
    return ir.Program(self.imports, fns)

  def visit_While(self, n):
    return ir.While(self.visit(n.test), *[self.visit(s) for s in n.body])

  # def visit_ListComp(self, n):
  #   expr = n.elt
  #   gens = n.generators
  #   stmts = []
  #   for g in gens:
  #     target = self.visit(g.target)
  #     iter = self.visit(g.iter)
  #     stmts.append()
  #   return ir.Block(stmts)

  def visit_Return(self, n):
    non_exprs = [ast.Name, ast.Num, ast.Str]
    if not n.value:
      v = None
    elif any(isinstance(n.value, a) for a in non_exprs):
      v = self.resolve(n.value)
    else:
      v = self.visit(n.value)
    return ir.Return(v)

  def visit_Break(self, n):
    return ir.Branch(ir.Branch.Type.Break)

  def visit_Continue(self, n):
    return ir.Branch(ir.Branch.Type.Continue)


def translate(fn):
  src = inspect.getsource(fn)
  tree = ast.parse(src)
  print(ast.dump(tree))
  e = Translator()
  v = e.visit(tree)
  return v

def translate_file(name):
  with open(name, "r") as source:
    tree = ast.parse(source.read())
    print(ast.dump(tree))
    e = Translator()
    v = e.visit(tree)
    return v
