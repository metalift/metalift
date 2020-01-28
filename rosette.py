from visitor import Visitor
import ir
import re

class RosetteTranslator(Visitor):

  def __init__(self):
    super().__init__(self.__class__.__name__)
    self.choose_fns = []
    self.choose_num = 0

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
    choose_num = self.choose_num
    args = []
    body = []
    for i in range(len(n.args)):
      args.append('e%d' % i)
      body.append('   [(= choose%d %d) e%d]\n' % (choose_num, i, i))

    self.choose_fns.append(('(define-symbolic choose%d integer?)\n' +
                            '(define (choose%d_fn %s) \n' +
                            '  (cond \n' +
                            '%s' +
                            '   [else (assert false)]))\n') %
                           (choose_num, choose_num, ' '.join(args), ''.join(body)))

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

  def visit_FnDecl(self, n):
    return '(define (%s %s) \n%s)\n' % \
      (n.name, ' '.join('%s' % self.visit(a) for a in n.args), self.visit(n.body))

  def visit_Assert(self, n):
    return '(assert %s)' % self.visit(n.expr)

  def count_vars(s: ir.Expr):
    if isinstance(s, ir.FnDecl):
      return []
    elif isinstance(s, ir.BinaryOp) or isinstance(s, ir.UnaryOp) or isinstance(s, ir.Call):
      vs = set()
      for v in s.args:
        vs.update(RosetteTranslator.count_vars(v))
      return vs
    elif isinstance(s, ir.Assert):
      return RosetteTranslator.count_vars(s.expr)
    elif isinstance(s, ir.Lit):
      return []
    elif isinstance(s, ir.Var):
      return [s]
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
        asserts.append(self.visit(s))
      else:
        stmts.append(self.visit(s))

    top_vars_decls = ['(define-symbolic %s integer?)' % v.name for v in top_vars]
    top_vars_names = [v.name for v in top_vars]

    return ('%s\n\n' + \
           '%s\n\n' + \
           '(define binding\n' + \
           '  (synthesize #:forall (list %s)\n' + \
           '              #:guarantee (and %s)))\n' + \
           'binding') % ('\n'.join(stmts), '\n'.join(top_vars_decls),
                                                      ' '.join(top_vars_names), ' '.join(asserts))


  def to_rosette(self, p):
    out = self.visit(p)
    return ('#lang rosette\n' +
            '(require rosette/lib/synthax)\n' +
            '%s\n%s' % ('\n'.join(self.choose_fns), out))


  # input should be of the form 'model\n [choose0 0]\n [choose1 0]...'
  def parse_output(self, s):
    out = re.findall(r'choose(\d+)\s(\d+)', str(s))
    return {int(key): int(val) for key, val in dict(out).items()}
