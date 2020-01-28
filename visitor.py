import ir

class Visitor:
  def __init__(self, passname):
    self.passname = passname

  def visit(self, node):
    method = 'visit_' + node.__class__.__name__
    if hasattr(self, method):
      return getattr(self, method)(node)
    else:
      return getattr(node, self.passname)(self)


class PassthruVisitor(Visitor):
  def __init__(self, passname):
    super().__init__(passname)

  def visit_BinaryOp(self, n):
    return ir.BinaryOp(n.op, *[self.visit(a) for a in n.args])

  def visit_UnaryOp(self, n):
    return ir.UnaryOp(n.op, *[self.visit(a) for a in n.args])

  def visit_Call(self, n):
    return ir.Call(n.name, *[self.visit(a) for a in n.args])

  def visit_Choose(self, n):
    return ir.Choose(*[self.visit(a) for a in n.args])

  def visit_Var(self, n):
    return n

  def visit_Lit(self, n):
    return n

  def visit_Field(self, n):
    return n

  def visit_Assign(self, n):
    return ir.Assign(self.visit(n.left), self.visit(n.righ))

  def visit_If(self, n):
    return ir.If(self.visit(n.cond), self.visit(n.conseq), self.visit(n.alt))

  # loop, while

  def visit_Return(self, n):
    return ir.Return(self.visit(n.body))

  def visit_Block(self, n):
    return ir.Block(*[self.visit(s) for s in n.stmts])

  def visit_FnDecl(self, n):
    return ir.FnDecl(n.name, [self.visit(a) for a in n.args], n.rtype, self.visit(n.body))

  def visit_Assert(self, n):
    return ir.Assert(self.visit(n.expr))

  def visit_Program(self, n):
    return ir.Program(n.imports, [self.visit(s) for s in n.stmts])