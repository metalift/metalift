import operator
from typing import Dict, Callable

from analysis import VarIdentifier
from cfg import CFGBuilder
from frontend import python
from ir import Block, num, Call, BinaryOp, While, Var, Stmt, If, Return, Lit, Choose, FnDecl, ExprStmt, true

from synth import synthesize, declare
from vcgen import VCGen, LoopTransformer
from visitor import PassthruVisitor

select_p = None  # int -> bool

def gen_predicates():
  global select_p

  n = Var('n', int)
  select_p = FnDecl('select_p', [n], bool, Block(Return(BinaryOp(operator.eq, n, num(2)))))

  declare(select_p)

# input a list of vars used in the code fragment and return a ML program
def inv_space_fn(ast: While, read_vars: Dict[str, Var], write_vars: Dict[str, Var]) -> Stmt:
  # i >= 0 and i <= len(l) and out::Select(l[i:]) = Select(l)

  out = write_vars['out']
  i = write_vars['i']
  l = read_vars['l']
  select_fn = Var(select_p.name, Callable[[int], bool])

  return Block(Return(BinaryOp(operator.and_,
                               BinaryOp(operator.ge, i, num(0)),
                               BinaryOp(operator.le, i, Call('list_length', l)),
                               BinaryOp(operator.eq,
                                        Call('list_concat', out, Call('Select', Call('list_tail', l, i), select_fn)),
                                        Call('Select', l, select_fn)))))


def ps_space_fn(ast: Stmt, read_vars: Dict[str, Var], write_vars: Dict[str, Var]) -> Stmt:
  # out = Select(l, select_p)
  out = write_vars['out']
  l = read_vars['l']
  select_fn = Var(select_p.name, Callable[[int], bool])

  return Block(Return(BinaryOp(operator.eq, out, Call('Select', l, select_fn))))



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

gen_predicates()

r = synthesize(r, l, info, inv_space_fn, ps_space_fn)
#
# # replace the body of the original fn with that of the synthesized versions
# lm = CodeGenerator().visit(FnDecl(lambda_m.name, lambda_m.args, lambda_m.rtype, r.fns[lambda_m.name].body))
# lr = CodeGenerator().visit(FnDecl(lambda_r.name, lambda_r.args, lambda_r.rtype, r.fns[lambda_r.name].body))
#
# s = r.fns['input_ps'].body.stmts[0].body  # an AND expr
# body = Block(ExprStmt(s), Return(Var('rv', int)))
# c = CodeGenerator().visit(FnDecl(fn.name, fn.args, fn.rtype, body))
# print('final code:\n%s\n\n%s\n\n%s' % (lm, lr, c))

