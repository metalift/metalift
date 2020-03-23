import operator
from typing import Dict

from cfg import CFGBuilder
from frontend import python
from ir import Block, num, Call, BinaryOp, While, Var, Stmt, If, Return, Lit, Choose

from synth import synthesize
from vcgen import VCGen, LoopTransformer
from visitor import PassthruVisitor

# input a list of vars used in the code fragment and return a ML program
def inv_space_fn1(ast: While, read_vars: Dict[str, Var], write_vars: Dict[str, Var]) -> Stmt:
  sum = write_vars["sum"]
  i = write_vars["i"]
  n = read_vars["n"]

  # i <= n && sum = my_sum(i)
  # if i <= n: i >= 0 and sum = my_sum(i)
  # else: sum = 0
  #
  return Block(If(BinaryOp(operator.le, i, n),
                  Return(BinaryOp(operator.and_, BinaryOp(operator.ge, i, num(0)),
                                                 BinaryOp(operator.eq, sum, Call("my_sum", i)))),
                  Return(BinaryOp(operator.eq, sum, num(0)))))

def inv_space_fn2(ast: While, read_vars: Dict[str, Var], write_vars: Dict[str, Var]) -> Stmt:
  sum = write_vars["sum"]
  i = write_vars["i"]
  n = read_vars["n"]

  # i <= n && sum = my_sum(i)
  # if i <= n: i >= 0 and sum = my_sum(choose(i, n))
  # else: sum = 0
  #
  return Block(If(BinaryOp(operator.le, i, n),
                  Return(BinaryOp(operator.and_, BinaryOp(operator.ge, i, num(0)),
                                                 BinaryOp(operator.eq, sum, Call("my_sum", Choose(n, i))))),
                  Return(BinaryOp(operator.eq, sum, num(0)))))


def ps_space_fn1(ast: Stmt, read_vars: Dict[str, Var], write_vars: Dict[str, Var]) -> Stmt:
  sum = write_vars["sum"]
  rv = write_vars["rv"]
  n = read_vars["n"]

  # if 0 <= n: sum = my_sum(n) and rv = sum
  # else: sum = 0 and rv = sum
  #
  return Block(If(BinaryOp(operator.le, num(0), n),
                  Return(BinaryOp(operator.and_, BinaryOp(operator.eq, sum, Call("my_sum", n)),
                                                 BinaryOp(operator.eq, rv, sum))),
                  Return(BinaryOp(operator.and_, BinaryOp(operator.eq, sum, num(0)),
                                                 BinaryOp(operator.eq, rv, sum)))))


class CodeGenerator(PassthruVisitor):
  def __init__(self, orig_fn):
    super().__init__(self.__class__.__name__)
    self.orig_fn = orig_fn

  def visit_Var(self, n):
    return n.name

  def visit_Lit(self, n: Lit):
    return str(n.val)

  def visit_BinaryOp(self, n: BinaryOp):
    ops = { operator.add: "+", operator.sub: "-", operator.eq: "=", operator.__le__: "<=", operator.and_: "and"}
    left, right = n.args[0], n.args[1]
    if n.op == operator.and_:
      return self.visit(left) + "\n    " + self.visit(right)
    else:
      return "%s %s %s" % (self.visit(left), ops[n.op], self.visit(right))

  def visit_If(self, n: If):
    return "if %s:\n    %s\n  else:\n    %s" % (self.visit(n.cond), self.visit(n.conseq), self.visit(n.alt))

  def visit_Return(self, n: Return):
    return self.visit(n.body)

  def visit_Block(self, n: Block):
    return "\n".join("  " + self.visit(s) for s in n.stmts)

  def visit_FnDecl(self, n):
    return "def %s(%s):\n%s\n  return rv" % (self.orig_fn.name, ", ".join(self.visit(a) for a in self.orig_fn.args),
                                             self.visit(n.body))

def codegen(ps, orig_fn):
  return CodeGenerator(orig_fn).visit(ps)


### Main Compiler ###

t = python.translate_file("input.py")
l = python.translate_file("udo.py")

fn = t.fns["input"]

c = CFGBuilder()
c.construct_cfg(fn)
(r, info) = LoopTransformer(c).visit(fn)
#print("after loop transform: %s" % r)

r = VCGen().visit(r)
#print("after vcgen: %s" % r)

r = synthesize(r, l, info, inv_space_fn1, ps_space_fn1)
#print("after synthesis: %s" % r)

c = codegen(r.fns["input_ps"], fn)
print("final code:\n%s" % c)
