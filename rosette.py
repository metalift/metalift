import operator

from visitor import Visitor, PassthruVisitor
import ir
import re


class RecursiveTranslator(PassthruVisitor):
  def __init__(self, call):
    super().__init__(self.__class__.__name__)
    self.call = call

  def visit_Return(self, n):
    return ir.ExprStmt(ir.BinaryOp(operator.eq, self.call, self.visit(n.body)))


class RosetteTranslator(Visitor):

  def __init__(self, synthesis, max_num=1):
    super().__init__(self.__class__.__name__)
    self.choose_fns = []
    self.choose_num = 0
    self.synthesis = synthesis  # synthesis or verify
    self.max_num = max_num
    self.sym_vars = set()  # symbolic vars to be declared, in case there is overlap

  def visit_BinaryOp(self, n):
    op = None
    if isinstance(n.op, ir.Choose):
      return '(%s %s)' % (self.visit(n.op), ' '.join(self.visit(a) for a in n.args))
    else:
      return ir.BinaryOp.to_rktfn(n.op, *[self.visit(a) for a in n.args])

  def visit_UnaryOp(self, n):
    return ir.UnaryOp.to_rktfn(n.op, *[self.visit(a) for a in n.args])

  def visit_Call(self, n):
    return '(%s %s)' % (n.name, ' '.join(self.visit(a) for a in n.args))

  def visit_Choose(self, n):
    if not self.synthesis:
      raise TypeError('Choose should not appear in verify')

    choose_num = self.choose_num
    args = []
    body = []
    for i in range(len(n.args)):
      args.append('e%d' % i)
      body.append('   [(= choose%d %d) e%d]\n' % (choose_num, i, i))

    self.choose_fns.append(('(define (choose%d_fn %s) \n' +
                            '  (cond \n' +
                            '%s' +
                            '   [else (assert false)]))\n') %
                           (choose_num, ' '.join(args), ''.join(body)))
    self.sym_vars.add(ir.Var('choose%d' % choose_num, int))

    self.choose_num += 1
    return '(choose%d_fn %s)' % (choose_num, ' '.join(self.visit(a) for a in n.args))

  def visit_Var(self, n):
    return str(n.name)

  def visit_Lit(self, n):
    if n.type == bool:
      return 'true' if n.val else 'false'
    else:
      return str(n.val)

  def visit_Field(self, n):
    if n.target == 'operator' and n.name == 'add':
      return '+'
    elif n.target == 'operator' and n.name == 'sub':
      return '-'
    else:
      raise TypeError('NYI: %s' % self)


  def visit_Assign(self, n):
    return '(define %s %s)' % (self.visit(n.left), self.visit(n.right))

  def visit_If(self, n):
    return '(if %s %s %s)' % (self.visit(n.cond), self.visit(n.conseq), self.visit(n.alt))

  # loop, while

  def visit_Return(self, n):
    return '%s' % self.visit(n.body)

  def visit_Block(self, n):
    return '(begin %s)' % ('\n'.join(self.visit(s) for s in n.stmts))

  def visit_ExprStmt(self, n):
    return '%s' % self.visit(n.expr)

  def visit_FnDecl(self, n):
    # hack for now: translate fn defs if synthesis, or invariants, and postconditions (assuming they are not recursive)
    if self.synthesis or n.name.startswith('inv') or n.name == 'ps':
      return '(define (%s %s) \n%s)\n' % \
        (n.name, ' '.join('%s' % self.visit(a) for a in n.args), self.visit(n.body))

    else:  # translate function definitions to UF in verification
      self.sym_vars.update(n.args)

      call = ir.Call(n.name, *n.args)
      body = RecursiveTranslator(call).visit(n.body)

      return ('(define-symbolic %s (~> %s %s))\n' +
              '(assert (forall (list %s)\n%s))\n') % \
             (n.name, ' '.join(ir.Expr.rkttype_fn(a.type) for a in n.args), ir.Expr.rkttype_fn(n.rtype),
              ' '.join(a.name for a in n.args), self.visit(body))


  def visit_Assert(self, n):
    if self.synthesis:
      return '(assert %s)' % self.visit(n.expr)
    else:
      return self.visit(n.expr)

  @staticmethod
  def count_vars(s: ir.Expr):
    if isinstance(s, ir.FnDecl):
      return set()
    elif isinstance(s, ir.BinaryOp) or isinstance(s, ir.UnaryOp) or isinstance(s, ir.Call):
      vs = set()
      for v in s.args:
        vs.update(RosetteTranslator.count_vars(v))
      return vs
    elif isinstance(s, ir.Assert):
      return RosetteTranslator.count_vars(s.expr)
    elif isinstance(s, ir.If):
      return RosetteTranslator.count_vars(s.cond).union(RosetteTranslator.count_vars(s.conseq))\
                                                 .union(RosetteTranslator.count_vars(s.alt))
    elif isinstance(s, ir.Lit):
      return set()
    elif isinstance(s, ir.Var):
      return {s}
    else:
      raise TypeError('NYI: %s of type %s' % (s, type(s)))

  def visit_Program(self, n):
    # parameters in top level stmts that are not func decls should be declared as symbolic
    top_vars = set()
    for s in n.stmts:
      top_vars.update(RosetteTranslator.count_vars(s))

    stmts = []
    asserts = []
    for s in n.stmts:
      if isinstance(s, ir.Assert):
        asserts.append(s)
      else:
        stmts.append(self.visit(s))

    if self.synthesis:
      sym_vars_decls = ['(define-symbolic %s %s)' % (v.name, ir.Expr.rkttype_fn(v.type)) for v in self.sym_vars]
      # distinguish between sym vars and those that need to be range limited
      top_vars_decls = ['[%s (range %s)]' % (v.name, self.max_num) for v in top_vars]

      return ('%s\n\n' +
              '%s\n\n' +
             '(define binding\n' +
             '  (solve (for (%s) \n' +
             '           (and %s))))\n' +
             'binding') % ('\n'.join(sym_vars_decls), '\n'.join(stmts),
                           ' '.join(top_vars_decls), ' '.join([self.visit(a) for a in asserts]))

    else:  # verification
      self.sym_vars.update(top_vars)
      top_vars_decls = ['(define-symbolic %s %s)' % (v.name, ir.Expr.rkttype_fn(v.type)) for v in self.sym_vars]

      top_vars_names = ' '.join(v.name for v in top_vars)
      fn_decls = [self.visit(s) for s in n.stmts if isinstance(s, ir.FnDecl)]

      # add forall and negation to asserts
      translated = [self.visit(s) for s in n.stmts if not isinstance(s, ir.FnDecl)]
      return ('%s\n\n' + '%s\n\n' + '(assert (forall (list %s) (not\n  (and\n    %s))))\n\n(solve (void))') % \
              ('\n'.join(top_vars_decls), '\n'.join(fn_decls), top_vars_names, '\n    '.join(translated))


  def to_rosette(self, p):
    out = self.visit(p)
    return ('#lang rosette\n' +
            '(require rosette/lib/synthax)\n' +
            '%s\n%s' % ('\n'.join(self.choose_fns), out))


  # input should be of the form 'model\n [choose0 0]\n [choose1 0]...'
  def parse_output(self, s):
    out = re.findall(r'choose(\d+)\s(\d+)', str(s))
    return {int(key): int(val) for key, val in dict(out).items()}
