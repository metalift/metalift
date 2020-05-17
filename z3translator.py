import collections
import operator
import typing

from rosette import RosetteTranslator
from visitor import Visitor, PassthruVisitor
import ir

class RecursiveTranslator(PassthruVisitor):
  def __init__(self, call):
    super().__init__(self.__class__.__name__)
    self.call = call

  def visit_Return(self, n):
    return ir.ExprStmt(ir.BinaryOp(operator.eq, self.call, self.visit(n.body)))


class Specializer(PassthruVisitor):
  def __init__(self, call: ir.Call):
    super().__init__(self.__class__.__name__)
    self.call = call
    self.to_specialize = set()

  def run(self):
    c = self.visit(self.call)
    return c, self.to_specialize

  def visit_Call(self, n):
    new_args = [self.visit(a) for a in n.args]
    new_name = n.name
    fn_args = []

    final_args = []
    for a in new_args:
      if a.type == collections.abc.Callable:
        new_name = '%s_%s' % (new_name, a.name)
        fn_args.append(a)
      else:
        final_args.append(a)

    if fn_args:
      self.to_specialize.add((n.name, tuple(fn_args)))

    return ir.Call(new_name, *final_args)

class Generator(PassthruVisitor):
  def __init__(self, fn: ir.FnDecl, specialize_for: typing.List[ir.Var]):
    super().__init__(self.__class__.__name__)
    self.fn = fn
    fn_args = [a for a in fn.args if a.type == collections.abc.Callable]
    self.actuals = dict(zip(fn_args, specialize_for))
    self.actuals_name = dict(zip([f.name for f in fn_args], specialize_for))
    self.specialize_for = specialize_for

  def run(self):
    new_name = self.fn.name
    for a in self.specialize_for:
      new_name = "%s_%s" % (new_name, a.name)
    new_args = [a for a in self.fn.args if a.type != collections.abc.Callable]
    return ir.FnDecl(new_name, new_args, self.fn.rtype, self.visit(self.fn.body))

  def visit_Var(self, n):
    if n in self.actuals:
      return self.actuals[n]
    else:
      return n

  def visit_Call(self, n):
    new_args = [self.visit(a) for a in n.args]
    #print("call: %s, %s " % (n, self.actuals))
    new_name = self.actuals_name[n.name].name if n.name in [k.name for k in self.actuals.keys()] else n.name
    return ir.Call(new_name, *new_args)


class Z3Translator(Visitor):

  def __init__(self):
    super().__init__(self.__class__.__name__)
    self.sym_vars = set()  # symbolic vars to be declared, in case there is overlap
    self.specialize = set()

  def visit_BinaryOp(self, n: ir.BinaryOp):
    if n.op == operator.add:  # distinguish between list concat and +
      # XXX
      if typing.get_origin(n.args[1].type) == list or typing.get_origin(n.args[0].type) == list:
        return '(list_concat %s)' % ' '.join([self.visit(a) for a in n.args])
      else:
        return ir.BinaryOp.to_z3fn(n.op, *[self.visit(a) for a in n.args])
    else:
      return ir.BinaryOp.to_z3fn(n.op, *[self.visit(a) for a in n.args])

  def visit_UnaryOp(self, n):
    return ir.UnaryOp.to_rktfn(n.op, *[self.visit(a) for a in n.args])

  def visit_Call(self, n):
    (n, fns) = Specializer(n).run()
    if fns:
      #print("renamed: %s, need to spec: %s" % (n, fns))
      self.specialize.update(fns)

    return '(%s %s)' % (n.name, ' '.join(self.visit(a) for a in n.args))

  def visit_Choose(self, n):
    raise TypeError('Choose should not appear in verify')

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

  # list operations
  def visit_ListConstructor(self, n: ir.ListConstructor):
    if len(n.exprs) == 0:  # empty list ctor
      return '(as nil %s)' % ir.Expr.z3type_fn(n.type)
    else:
      l = '(as nil %s)' % ir.Expr.z3type_fn(n.type)
      for e in reversed(n.exprs):
        l = '(cons %s %s)' % (self.visit(e), l)
      return l

  def visit_ListAccess(self, n: ir.ListAccess):
    return '(list_get %s %s)' % (self.visit(n.target), self.visit(n.index))

  # statements
  def visit_If(self, n):
    return '(ite %s %s %s)' % (self.visit(n.cond), self.visit(n.conseq), self.visit(n.alt))

  # loop, while

  def visit_Return(self, n):
    return '%s' % self.visit(n.body)

  def visit_Block(self, n):
    assert(len(n.stmts) == 1)
    return self.visit(n.stmts[0])

  def visit_ExprStmt(self, n):
    return '%s' % self.visit(n.expr)

  def visit_FnDecl(self, n: ir.FnDecl):
    param_types = (ir.Expr.z3type_fn(a.type) for a in n.args)
    param_names = (self.visit(a) for a in n.args)

    return ('(%s ( %s ) %s)' %
            (n.name, ' '.join(['(%s %s)' % (n,t) for (n,t) in zip(param_names, param_types)]), ir.Expr.z3type_fn(n.rtype)),
            self.visit(n.body))

  def visit_Assert(self, n):
    return "(push)\n(assert (not %s))\n(check-sat)\n(pop)\n\n" % self.visit(n.expr)

  def visit_Program(self, n):
    # parameters in top level stmts that are not func decls should be declared as symbolic
    top_vars = set()
    for s in n.stmts:
      top_vars.update(RosetteTranslator.count_vars(s))

    # identify the higher order functions
    ho_fns = dict([(f.name, f) for f in n.stmts if
                   isinstance(f, ir.FnDecl) and any(p.type == collections.abc.Callable for p in f.args)])

    self.sym_vars.update(top_vars)
    top_vars_decls = ['(declare-const %s %s)' % (v.name, ir.Expr.z3type_fn(v.type)) for v in self.sym_vars]

    # translate the non higher-order functions, and see if any of them needs to be specialized
    (fn_names, fn_defs) = map(list, zip(*[self.visit(s) for s in n.stmts if isinstance(s, ir.FnDecl) and s.name not in ho_fns]))

    # generate the specializations
    done = set()
    while bool(self.specialize):
      (fn_name, sp_for) = self.specialize.pop()
      if (fn_name, sp_for) not in done:
        fn = ho_fns[fn_name]
        specialized = Generator(fn, sp_for).run()
        sp_fn = self.visit(specialized)
        print("post visit: %s\n%s" % sp_fn)
        fn_names.append(sp_fn[0])
        fn_defs.append(sp_fn[1])
        done.add((fn_name, sp_for))
      else:
        print('%s for %s already generated' % (fn_name, sp_for))

    # add forall and negation to asserts
    translated = [self.visit(s) for s in n.stmts if not isinstance(s, ir.FnDecl)]

    with open('../../smtlib/list.z3', 'r') as f:
      list_axioms = f.read()

    with open('../../smtlib/mapreduce.z3', 'r') as f:
      mr_axioms = f.read()

    fn_decls = '(define-funs-rec\n(\n%s\n)\n(\n%s\n))' % ('\n'.join(fn_names), '\n'.join(fn_defs))

    return '%s\n\n%s\n\n%s\n\n%s\n\n%s\n\n' % \
           (list_axioms, fn_decls, mr_axioms, '\n'.join(top_vars_decls), '\n'.join(translated))


  def to_z3(self, p):
    out = self.visit(p)
    return out
