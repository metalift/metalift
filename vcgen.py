import copy
import functools
from collections import deque

from analysis import VarIdentifier
from visitor import Visitor, PassthruVisitor
from cfg import CFGBuilder
import ir
import operator

class LoopTransformer(PassthruVisitor):
  def __init__(self, cfg: CFGBuilder):
    super().__init__(self.__class__.__name__)
    self.cfg = cfg
    self.fns = []
    self.info = {}  # maps fn to (read vars, write vars)
    self.loops = deque()  # (call to inv fn, {loop back stmts})
    self.inv_num = 0
    self.ps = None

  def visit_Assign(self, n):
    if self.loops and n in self.loops[-1][1]:
      return ir.Block(n, ir.Assert(self.loops[-1][0]), ir.Assert(ir.false()))
    else:
      return n

  # if -- take default behavior

  def inv(self, vars, body=ir.Block()):
    name = "inv_" + str(self.inv_num)
    self.inv_num = self.inv_num + 1
    inv_decl = ir.FnDecl(name, vars, bool, body)
    self.fns.append(inv_decl)
    return inv_decl

  @staticmethod
  def is_inv_ps(fn: ir.FnDecl):
    return fn.name.startswith("inv_") or fn.name.endswith("_ps")

  def visit_While(self, n):
    vi = VarIdentifier()
    vi.visit(n)
    vars = vi.read_vars | vi.write_vars
    inv_decl = self.inv(vars)
    call = ir.Call(inv_decl.name, *vars)
    self.info[inv_decl] = (vi.read_vars, vi.write_vars)
    self.loops.append((call, self.cfg.preds[n, CFGBuilder.FlowType.LoopBack]))

    r = ir.Block(
      *[ir.Assert(call),
        ir.Havoc(*vi.write_vars),
        ir.Assume(call),
        ir.If(n.cond, self.visit(n.body)),
        ir.Assume(ir.UnaryOp(operator.not_, n.cond))])

    self.loops.pop()
    return r

  def visit_Branch(self, n):
    return ir.Block(*[ir.Assert(self.loops[-1][0]), ir.Assert(ir.false())])

  def visit_Return(self, n):
    if n.body:
      r = ir.Block(ir.Assign(ir.Var("rv", n.body.type), self.visit(n.body)))
    else:
      r = ir.Block()
    if self.loops:  # we are inside a loop
      r.stmts.append(ir.Assert(self.loops[-1][0]))
    r.stmts.extend([ir.Assert(self.ps), ir.Assert(ir.false())])
    return r

  def visit_FnDecl(self, n):
    vi = VarIdentifier()
    vi.visit(n.body)
    vars = vi.read_vars | vi.write_vars

    # if fn has a return value then add the return value var to write_vars
    if n.rtype is not None:
      vars.add(ir.Var("rv", n.rtype))

    ps = ir.FnDecl(n.name + '_ps', list(vars), bool, ir.Block())
    self.fns.append(ps)
    self.info[ps] = (vi.read_vars, vi.write_vars)
    self.ps = ir.Call(ps.name, *vars)

    # return a new program
    body = self.visit(n.body)
    return ir.Program(None, self.fns + [ir.FnDecl(n.name, n.args, n.rtype, body)]), self.info


class VCGen(Visitor):

  class State:
    def __init__(self):
      self.var = {}
      self.assumes = []
      self.fns = []
      self.asserts = []
      self.rv = None
      self.var_num = 0  # for havoc

    def __repr__(self):
      return 'vars: %s  \nrv: %s  \ncond: %s  \nfns: %s  \nasserts: %s' % \
             (self.var, self.rv, '\n'.join([str(a) for a in self.assumes]), '\n'.join([str(f) for f in self.fns]),
              '\n'.join([str(a) for a in self.asserts]))


  def __init__(self):
    super().__init__(self.__class__.__name__)
    self.state = VCGen.State()

  def visit_BinaryOp(self, n):
    if isinstance(n.op, ir.Expr):
      return ir.BinaryOp(self.visit(n.op), *[self.visit(a) for a in n.args])
    else:
      return ir.BinaryOp(n.op, *[self.visit(a) for a in n.args])

  def visit_UnaryOp(self, n):
    if isinstance(n.op, ir.Expr):
      return ir.UnaryOp(self.state.var[self.visit(n.op)], *[self.state.var[self.visit(a)] for a in n.args])
    else:
      return ir.UnaryOp(n.op, *[self.visit(a) for a in n.args])

  def visit_Call(self, n: ir.Call):
    # special cases for invariant and postcondition function calls
    if n.name.startswith("inv") or n.name.endswith("_ps") or \
      n.name == "list_length" or n.name == "list_concat":
      return ir.Call(n.name, *[self.visit(arg) for arg in n.args])
    else:
      raise TypeError('NYI: %s' % n)

  def visit_Choose(self, n):
    raise TypeError("choose should not appear in vcgen: %s" % n)

  def visit_Var(self, n):
    return self.state.var[n]

  def visit_Lit(self, n):
    return n

  # list operations
  def visit_ListConstructor(self, n: ir.ListConstructor):
    return ir.ListConstructor(*[self.visit(arg) for arg in n.args])


  def visit_ListAccess(self, n: ir.ListAccess):
    return ir.ListAccess(self.visit(n.target), self.visit(n.index), n.type)


  ## statements

  def visit_Assign(self, n: ir.Assign):
    if not isinstance(n.left, ir.Var):
      raise TypeError("lhs of assign is not a variable: %s" % n)
    print('xxx %s' % n)
    self.state.var[n.left] = self.visit(n.right)
    return True

  def visit_If(self, n: ir.If):
    cond = self.visit(n.cond)
    not_cond = ir.UnaryOp(operator.not_, cond)
    vars = copy.deepcopy(self.state.var)
    var_names = list(self.state.var.keys())
    rv = self.state.rv

    self.state.assumes.append(cond)
    conseq_cont = self.visit(n.conseq)
    conseq_vars = copy.deepcopy(self.state.var)
    conseq_rv = self.state.rv
    self.state.assumes.pop()
    self.state.var = vars

    if n.alt:
      self.state.assumes.append(not_cond)
      alt_cont = self.visit(n.alt)
      self.state.assumes.pop()

      if conseq_cont and alt_cont:
        # merge: only those vars in var_copy before either conseq and alt were executed matter
        # everything else declared inside conseq and alt are now out of scope
        new_vars = {}
        for v in var_names:
          conseq_val = conseq_vars[v]
          alt_val = self.state.var[v]
          if conseq_val == alt_val:
            new_vars[v] = conseq_val
          else:
            new_vars[v] = ir.If(cond, conseq_val, alt_val)

        if conseq_rv != self.state.rv:
          self.state.rv = ir.If(cond, conseq_rv, self.state.rv)

        self.state.var = new_vars
        print("merged vars: %s" % self.state.var)

      elif conseq_cont and not alt_cont:  # take everything from consequence
        self.state.var = {k:v for (k,v) in conseq_vars.items() if k in var_names}
        self.state.rv = conseq_rv
        self.state.assumes.append(cond)

      elif not conseq_cont and alt_cont:  # take everything from alternate
        self.state.var = {k:v for (k,v) in self.state.var.items() if k in var_names}
        self.state.assumes.append(not_cond)
        # rv is already set

      else:  # not conseq_cont and not alt_cont -- restore the original
        self.state.var = vars
        self.state.rv = rv

      return conseq_cont or alt_cont
    else:  # no alt, so must continue
      return True

  # loop, while
  def visit_While(self, n):
    raise TypeError("should not encounter while in vcgen: %s" % n)

  def visit_Return(self, n):
    raise TypeError("should not encounter return in vcgen: %s" % n)

  def visit_Havoc(self, n: ir.Havoc):
    for v in n.args:
      if not isinstance(v, ir.Var):
        raise TypeError("argument to havoc is not a variable: %s" % v)
      if v not in self.state.var:
        raise TypeError("variable is not in scope: %s" % v)
      self.state.var[v] = ir.Var(v.name + "_" + str(self.state.var_num), v.type)
      self.state.var_num = self.state.var_num + 1

    return True

  def visit_Assume(self, n: ir.Assume):
    if isinstance(n.expr, ir.Lit) and not n.expr.val:  # assume false -- stop
      return False
    else:
      self.state.assumes.append(self.visit(n.expr))
      return True

  def visit_Assert(self, n: ir.Assert):
    if isinstance(n.expr, ir.Lit) and not n.expr.val:  # assert false -- stop
      return False
    else:
      if self.state.assumes:
        assumes = functools.reduce(lambda c1, c2: ir.BinaryOp(operator.__and__, c1, c2), self.state.assumes)
        self.state.asserts.append(ir.Assert(ir.implies(assumes, self.visit(n.expr))))
      else:
        self.state.asserts.append(ir.Assert(self.visit(n.expr)))
      return True

  def visit_Block(self, n):
    for s in n.stmts:
      if not self.visit(s):
        return False
    return True

  def visit_FnDecl(self, n: ir.FnDecl):
    # initialize function arguments
    for arg in n.args:
      self.state.var[arg] = arg

    self.visit(n.body)

    return self.state.asserts

  def visit_Program(self, n: ir.Program):
    stmts = [d for d in n.stmts if isinstance(d, ir.FnDecl) and LoopTransformer.is_inv_ps(d)]
    for decl in n.stmts:
      if isinstance(decl, ir.FnDecl) and not LoopTransformer.is_inv_ps(decl):
        d = self.visit(decl)
        if isinstance(d, list):
          stmts.extend(d)
        else:
          stmts.append(d)

    return ir.Program(n.imports, stmts)
