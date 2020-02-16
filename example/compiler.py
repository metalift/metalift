import operator
from typing import Dict

from frontend import python
import ir
from synth import synthesize
from vcgen import VCGen
from visitor import PassthruVisitor

# input a list of vars used in the code fragment and return a ML program
def inv_space_fn1(ast: ir.While, read_vars: Dict[str, ir.Var], write_vars: Dict[str, ir.Var]) -> ir.Stmt:

  # if we have an interpreter this could be written simply as: return choose(False, True)
  #return ir.Block(ir.Return(ir.Choose(ir.Lit(False, bool), ir.Lit(True, bool))))

  sum = write_vars['sum']
  i = write_vars['i']
  n = read_vars['n']

  # i <= n && sum = my_sum(i)
  return ir.Block(ir.Return(ir.BinaryOp(operator.and_, ir.BinaryOp(operator.le, i, n),
                                                       ir.BinaryOp(operator.eq, sum, ir.Call('my_sum', i)))))

def ps_space_fn1(ast: ir.Stmt, read_vars: Dict[str, ir.Var], write_vars: Dict[str, ir.Var]) -> ir.Stmt:
  sum = write_vars['sum']
  # sum = my_sum(choose(i, n, sum))
  return ir.Block(ir.Return(ir.BinaryOp(operator.eq, sum, ir.Call('my_sum',
                                                                  ir.Choose(*read_vars.values())))))

# a fully expanded recursive space fn. haven't tested this yet.
# if we have an interpreter this could be written as:
# if depth == 0: return choose(*vars) + choose(*vars)
# else: return space_fn2(vars, depth-1) + space_fn2(vars, depth-1)
def space_fn2(ast: ir.While, read_vars: Dict[str, ir.Var], write_vars: Dict[str, ir.Var], depth: int) -> ir.Stmt:
  if depth == 0:
    return ir.Return(ir.BinaryOp(operator.add, ir.Choose(*read_vars), ir.Choose(*read_vars)))
  else:
    return ir.Return(ir.BinaryOp(operator.add, space_fn2(read_vars, depth - 1), space_fn2(read_vars, depth - 1)))

# same as space_fn2, but with a synthesized conditional that determines whether to recurse or not
# even if depth has not reached
# if depth == 0: return choose(*vars) + choose(*vars)
# else if choose(True, False): return space_fn2(vars, depth-1) + space_fn2(vars, depth-1)
# else: return choose(*vars) + choose(*vars)
def space_fn3(ast: ir.While, read_vars: Dict[str, ir.Var], write_vars: Dict[str, ir.Var], depth: int) -> ir.Stmt:
  if depth == 0:
    return ir.Return(ir.BinaryOp(operator.add, ir.Choose(*read_vars), ir.Choose(*read_vars)))
  else:  # return an ML AST
    cond = ir.Choose(ir.Lit(True, bool), ir.Lit(False, bool))
    cons = ir.Return(space_fn3(read_vars, 0))
    alt = ir.Return(ir.BinaryOp(operator.add, space_fn3(read_vars, depth - 1), space_fn3(read_vars, depth - 1)))
    return ir.If(cond, cons, alt)


class CodeGenerator(PassthruVisitor):
  def __init__(self):
    super().__init__(self.__class__.__name__)

  def visit_Var(self, n):
    return n.name

  def visit_Lit(self, n: ir.Lit):
    return str(n.val)

  def visit_Return(self, n: ir.Return):
    return 'return %s' % self.visit(n.body)

  def visit_Block(self, n: ir.Block):
    return '\n'.join('  ' + self.visit(s) for s in n.stmts)

  def visit_FnDecl(self, n):
    return 'def %s(%s):\n%s' % (n.name, ', '.join(self.visit(a) for a in n.args), self.visit(n.body))

def codegen(ps):
  return CodeGenerator().visit(ps)


t = python.translate_file('example/test.py')
print('t: %s' % t)

# target language definition (wip)
l = python.translate_file('example/udo.py')
print('l: %s' % l)

fn = t.fns['vctest']
vcgen = VCGen()
r = vcgen.visit(fn)
info = vcgen.info
print('after vcgen: %s' % r)

r = synthesize(r, l, info, inv_space_fn1, ps_space_fn1)
print('after synthesis: %s' % r)

c = codegen(r.fns['ps'])
print('final code: %s' % c)
