import ir
from visitor import PassthruVisitor

# labels each variable as either read, written, or both
class VarIdentifier(PassthruVisitor):
  def __init__(self):
    super().__init__(self.__class__.__name__)
    self.write_vars = set()
    self.read_vars = set()

  def visit_BinaryOp(self, n):
    return set().union(*[self.visit(a) for a in n.args])

  def visit_UnaryOp(self, n: ir.UnaryOp):
    return set().union(self.visit(n.arg))

  def visit_Call(self, n):
    return set().union(*[self.visit(a) for a in n.args])

  def visit_Choose(self, n):
    raise TypeError("Choose should not appear")

  def visit_Var(self, n):
    return {n}

  def visit_Lit(self, n):
    return set()

  # def visit_ListAccess(self, n):
  #   self.visit(n.target)

  def visit_Field(self, n):
    return {n}

  def visit_Assign(self, n):
    self.write_vars.add(n.left)
    self.read_vars.update(self.visit(n.right))
    return None

  def visit_If(self, n):
    self.read_vars.update(self.visit(n.cond))
    self.visit(n.conseq)
    self.visit(n.alt)
    return None

  # loop, while

  def visit_While(self, n):
    self.read_vars.update(self.visit(n.cond))
    self.visit(n.body)
    return None

  def visit_Return(self, n):
    if n.body:
      self.read_vars.update(self.visit(n.body))
      self.write_vars.add(ir.Var("rv", n.body.type))
    return None

  def visit_Block(self, n):
    for s in n.stmts:
      self.visit(s)
    return None

  def visit_FnDecl(self, n):
    self.visit(n.body)
    return None

  def visit_ExprStmt(self, n):
    self.visit(n.expr)
    return None

  def visit_Assert(self, n):
    self.visit(n.expr)
    return None

  def visit_Assume(self, n):
    self.visit(n.expr)
    return None