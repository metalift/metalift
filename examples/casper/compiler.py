import operator
from typing import Dict, Callable

from analysis import VarIdentifier
from cfg import CFGBuilder
from frontend import python
from ir import Block, num, Call, BinaryOp, While, Var, Stmt, If, Return, Lit, Choose, FnDecl, ExprStmt

from synth import synthesize, declare
from vcgen import VCGen, LoopTransformer
from visitor import PassthruVisitor

lambda_m = None  # int -> int
lambda_r = None  # (int, int) -> int

def gen_lambdas():
  global lambda_m, lambda_r

  n = Var('n', int)
  lambda_m = FnDecl('lambda_mapper', [n], int, Block(Return(BinaryOp(operator.mul, n, num(2)))))

  v1 = Var('v1', int)
  v2 = Var('v2', int)
  lambda_r = FnDecl('lambda_reducer', [v1, v2], int, Block(Return(BinaryOp(operator.add, v1, v2))))

  declare(lambda_m, lambda_r)


# input a list of vars used in the code fragment and return a ML program
def inv_space_fn(ast: While, read_vars: Dict[str, Var], write_vars: Dict[str, Var]) -> Stmt:
  sum = write_vars['sum']
  i = write_vars['i']
  l = read_vars['l']
  mapper_fn = Var(lambda_m.name, Callable[[int], int])
  reducer_fn = Var(lambda_r.name, Callable[[int, int], int])

  # i >= 0 and i <= len(l) and sum = Reduce(Map(l[0:i], map_f), reduce_f, 0)
  return Block(Return(BinaryOp(operator.and_,
                               BinaryOp(operator.ge, i, num(0)),
                               BinaryOp(operator.le, i, Call('list_length', l)),
                               BinaryOp(operator.eq, Choose(BinaryOp(operator.add, i, num(1)), sum),
                                        Call('reducer', Call('mapper', Call('list_take', l, i), mapper_fn), reducer_fn, num(0))))))


def ps_space_fn(ast: Stmt, read_vars: Dict[str, Var], write_vars: Dict[str, Var]) -> Stmt:
  l = read_vars['l']
  sum = write_vars['sum']
  rv = write_vars['rv']
  mapper_fn = Var(lambda_m.name, Callable[[int], int])
  reducer_fn = Var(lambda_r.name, Callable[[int, int], int])

  # pc: sum = Reduce(Map(l, map_f), reduce_f, 0) and rv = sum
  return Block(Return(BinaryOp(operator.and_,
                               BinaryOp(operator.eq, sum,
                                        Call('reducer', Call('mapper', l, mapper_fn), reducer_fn, num(0))),
                               BinaryOp(operator.eq, rv, sum))))


class CodeGenerator(PassthruVisitor):
  def __init__(self):
    super().__init__(self.__class__.__name__)

  def visit_Var(self, n):
    return n.name

  def visit_Lit(self, n: Lit):
    return str(n.val)

  def visit_BinaryOp(self, n: BinaryOp):
    ops = { operator.add: '+', operator.sub: '-', operator.eq: '=', operator.mul: '*',
            operator.__le__: '<=', operator.and_: 'and'}
    left, right = n.args[0], n.args[1]
    if n.op == operator.and_:
      return self.visit(left) + '\n  ' + self.visit(right)
    else:
      return '%s %s %s' % (self.visit(left), ops[n.op], self.visit(right))

  def visit_ExprStmt(self, n: ExprStmt):
    return self.visit(n.expr)

  def visit_Return(self, n: Return):
    return 'return %s' % self.visit(n.body)

  def visit_Block(self, n: Block):
    return '\n'.join('  ' + self.visit(s) for s in n.stmts)

  def visit_FnDecl(self, n):
    return 'def %s(%s):\n%s' % (n.name, ', '.join(self.visit(a) for a in n.args), self.visit(n.body))

### Main Compiler ###

t = python.translate_file('input.py')
l = python.translate_file('udo.py')

fn = t.fns['input']

c = CFGBuilder()
c.construct_cfg(fn)

vi = VarIdentifier()
vi.visit(fn)
print('read: %s\n write: %s' % (vi.read_vars, vi.write_vars))
(r, info) = LoopTransformer(c).visit(fn)
print('after loop transform: %s' % r)

r = VCGen().visit(r)
print('after vcgen: %s' % r)

gen_lambdas()

r = synthesize(r, l, info, inv_space_fn, ps_space_fn)

# replace the body of the original fn with that of the synthesized versions
lm = CodeGenerator().visit(FnDecl(lambda_m.name, lambda_m.args, lambda_m.rtype, r.fns[lambda_m.name].body))
lr = CodeGenerator().visit(FnDecl(lambda_r.name, lambda_r.args, lambda_r.rtype, r.fns[lambda_r.name].body))

s = r.fns['input_ps'].body.stmts[0].body  # an AND expr
body = Block(ExprStmt(s), Return(Var('rv', int)))
c = CodeGenerator().visit(FnDecl(fn.name, fn.args, fn.rtype, body))
print('final code:\n%s\n\n%s\n\n%s' % (lm, lr, c))
