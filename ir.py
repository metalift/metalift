import importlib
import operator
from abc import abstractmethod
from typing import List

from state import State, Frame

# metalift IR. There are two base classes: Expr's that return a typed value,
# and Stmt's that do not return anything.

class Expr:
  sktype_fn = None

  def __init__(self, *args):
    self.args = args

  @abstractmethod
  def symeval(self, state):
    pass


class BinaryOp(Expr):
  valid_ops = []
  to_skfn = None
  to_rktfn = None

  def __init__(self, op, *args):
    self.op = op
    self.args = args
    if not isinstance(op, Choose) and not any(op == o for o in BinaryOp.valid_ops):
      raise TypeError('unsupported op: %s' % op)

    # types = {a.type for a in args}
    # if len(types) != 1:
    #   raise TypeError('not all arguments are of the same type: %s' % self.args)

    self.type = None

  def __repr__(self):
    return '%s(%s)' % (self.op, ', '.join(str(x) for x in self.args))

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.op == other.op and self.args == other.args

  def symeval(self, s: Frame):
    args = [arg.symeval(s) for arg in self.args]
    if any(isinstance(a, Var) for a in args): # symbolic
      return BinaryOp(self.op, args)
    else:
      return self.op(*args)


class UnaryOp(Expr):
  valid_ops = []
  to_skfn = None
  to_rktfn = None

  def __init__(self, op, arg):
    super().__init__(arg)
    self.op = op
    self.arg = arg
    if not any(op == o for o in UnaryOp.valid_ops):
      raise TypeError('only supported ops are: %s' % BinaryOp.valid_ops)
    self.type = arg.type

  def __repr__(self):
    return '%s %s' % (self.op, self.arg)

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.op == other.op and self.arg == other.arg


class Call(Expr):
  def __init__(self, name, *args):
    super().__init__(*args)
    self.name = name
    self.args = args

  def __repr__(self):
    return '%s(%s)' % (self.name, ', '.join(str(x) for x in self.args))

  def symeval(self, s: State):
    args = [a.symeval(s) for a in self.args]
    fn = self.name.symeval(s)
    if isinstance(fn, Expr) or any(isinstance(a, Expr) for a in args):  # symbolic
      raise TypeError('NYI: %s' % self)
    else:
      return fn(*args)

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.name == other.name and self.args == other.args


class Choose(Expr):
  def __init__(self, *args):
    super().__init__()
    self.args = args
    types = {a.type for a in args}
    if len(types) != 1:  # need to check for subtypes
      raise TypeError('not all arguments are of the same type: %s' % self.args)
    self.type = types.pop()

  def __repr__(self):
    return 'choose(%s)' % ', '.join(str(x) for x in self.args)

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.op == other.op and self.args == other.args

# ignore this for now
def gen_Expr(name, types, ops):
  def init(self, op, *args):
    Expr.__init__(self, op, args)
    for a in args:
      if not isinstance(a, self.valid_types):
        raise TypeError('only supported types are: ' + str(self.valid_types))

    if not any(op == o for o in self.valid_ops):
      raise TypeError('only supported ops are: ' + str(self.valid_ops))

  return type(name, (Expr, ), {'__init__': init, 'valid_types': types, 'valid_ops': ops})


class Var(Expr):
  valid_types = []

  def __init__(self, name, t):
    if not any(issubclass(t, vt) for vt in Var.valid_types):
      raise TypeError('only supported vars of type: %s and not %s' % (Var.valid_types, t))
    self.name = name
    self.type = t

  def __repr__(self):
    return '%s:%s' % (self.name, self.type.__name__)

  def symeval(self, s: State):
    return s.vars[self.name]

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.name == other.name and self.type == other.type

  def __hash__(self):
    return hash(self.name + str(self.type))

class Lit(Expr):
  valid_types = []

  def __init__(self, val, t):
    self.val = val
    if not any(isinstance(val, ty) for ty in Lit.valid_types):
      raise TypeError('only supported types are: %s but not %s' % (str(Lit.valid_types), str(val)))
    self.type = t

  def __repr__(self):
    return '%s:%s' % (str(self.val), self.type.__name__)

  def symeval(self, s):
    return self.val

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.type == other.type and self.val == other.val

# python specific
class Unpack(Expr):
  def __init__(self, val):
    self.val = val

  def __repr__(self):
    return 'unpack(%s)' % str(self.val)


class Field(Expr):
  def __init__(self, target, name):
    self.target = target
    self.name = name
    self.type = None  # XXX

  def __repr__(self):
    return '%s.%s' % (self.target, self.name)

  def symeval(self, s):
    if isinstance(self.target, str) and isinstance(self.name, str):
      return eval(str(self))
    else:
      raise TypeError('NYI: %s' % self)

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.target == other.target and self.name == other.name \
           and self.type == other.type

def gen_Lit(name, types):

  def init(self, val):
    Lit.__init__(self, val)
    if not isinstance(val, self.valid_types):
      raise TypeError('only supported types are: ' + str(self.valid_types))

  return type(name, (Lit,), {'__init__': init, 'valid_types': types})


class Stmt:
  def __init__(self, *args):
    self.args = args

class Assign(Stmt):
  def __init__(self, left, right):
    super().__init__(left, right)
    self.left = left
    self.right = right
    if not isinstance(left, Var):
      raise TypeError('left hand side of assign must be a Var rather than %s' % left)

  def __repr__(self):
    return '%s = %s;\n' % (self.left, self.right)

  def symeval(self, s: State):
    s.vars[self.left.name] = self.right.symeval(s)
    return True


class If(Stmt):
  def __init__(self, cond, conseq, alt = None):
    super().__init__(cond, conseq, alt)
    self.cond = cond
    self.conseq = conseq
    self.alt = alt
    # if cond.type != bool:
    #   raise TypeError('cond of If must be a BinaryOp rather than %s' % cond)
    # if not isinstance(conseq, Stmt):
    #  raise TypeError('conseq of Stmt must be a Stmt rather than %s' % conseq)
    # if alt is not None and not isinstance(alt, Stmt):
    #  raise TypeError('alt of Stmt must be a Stmt rather than %s' % alt)

  def __repr__(self):
    return 'if (%s) %s \nelse %s' % (self.cond, self.conseq, self.alt)


class Loop(Stmt):
  def __init__(self, cond, body):
    super().__init__(cond, body)

class While(Loop):
  def __init__(self, cond, *body):
    super().__init__(cond, Block(*body))  # block also expects a variable number of arguments
    self.cond = cond
    self.body = Block(*body)

  def __repr__(self):
    return 'while (%s) { %s }' % (self.cond, self.body)

class Return(Stmt):
  def __init__(self, body):
    super().__init__(body)
    self.body = body

  def __repr__(self):
    return 'return %s;' % self.args[0]

  def symeval(self, s: State):
    r = self.body.symeval(s)
    s.rv = s.vars[r] if isinstance(r, Var) else r
    return False


class Block(Stmt):
  stmt_types = []
  def __init__(self, *stmts):
    super().__init__(stmts)
    self.stmts = stmts
    for s in stmts:
      if not any(isinstance(s, t) for t in Block.stmt_types):
        raise TypeError('Block body needs to be a %s rather than %s: %s' % (Block.stmt_types, type(s), s))

  def __repr__(self):
    return '{ %s }' % ('\n'.join(repr(s) for s in self.stmts))

  def symeval(self, s: State):
    for stmt in self.stmts:
      if not stmt.symeval(s):
        return False
    return True


class FnDecl(Stmt):
  stmt_types = []

  def __init__(self, name: str, args: List[Var], rtype: type, body: Block):
    super().__init__(args)
    self.name = name
    self.args = args
    self.body = body
    self.rtype = rtype
    if not isinstance(body, Block):
      raise TypeError('fn decl body must be a block but not a %s' % body)
    if not all(isinstance(a, Var) for a in args):
      raise TypeError('fn args must be a Var but not a %s' % args)

  def __repr__(self):
    return '%s(%s) \n%s\n' % (self.name, ', '.join(repr(a) for a in self.args), self.body)

  def symeval(self, s: State):
    self.body.symeval(s)
    return s.rv

# e.g., a single function call w/o return values
class ExprStmt(Stmt):
  def __init__(self, e: Expr):
    super().__init__(e)
    self.expr = e

  def __repr__(self):
    return '(%s)' % self.e

class Assert(Stmt):
  def __init__(self, e: Expr):
    super().__init__(e)
    self.expr = e

  def __repr__(self):
    return 'assert(%s)' % self.expr


class Program:
  stmt_types = []

  def __init__(self, imports, stmts):
    self.imports = imports
    self.fns = {}
    self.stmts = stmts
    for s in stmts:
      #if not any(isinstance(s, t) for t in Program.stmt_types):
      #  raise TypeError('only supported types are: %s but not %s' % (self.stmt_types, s))
      if isinstance(s, FnDecl):
        self.fns[s.name] = s

  def __repr__(self):
    return '\n'.join([str(s) for s in self.stmts])

  def symeval(self, fn_name, params={}):
    for mod in self.imports:
      globals()[mod] = importlib.import_module(mod)

    fn = self.fns[fn_name]
    s = State()
    for a in fn.args:
      if a.name in params:
        s.vars[a.name] = params[a.name]
      else:
        s.vars[a.name] = Var(a.name, a.type)
    return fn.symeval(s)

# ignore this for now
def gen_Stmt(name, types, repr_fn):
  def init(self, *args):
    Stmt.__init__(self, args)
    for a in args:
      if not isinstance(a, self.valid_types):
        raise TypeError('only supported types are: %s' % self.valid_types)

  return type(name, (Stmt, ), {'__init__': init, 'valid_types': types, '__repr__': repr_fn})

def sktype_fn(t: type) -> str:
  if t == int: return 'int'
  elif t == bool: return 'bit'
  else: raise TypeError('NYI: %s' % t)

def binary_skfn(op, *args) -> str:
  if op == operator.add: return '+'.join(args)
  elif op == operator.sub: return '-'.join(args)
  elif op == operator.mul: return '*'.join(args)
  elif op == operator.truediv: return '/'.join(args)
  elif op == operator.mod: return '%'.join(args)
  elif op == operator.eq: return '='.join(args)
  else: raise TypeError('NYI: %s' % op)

def binary_rktfn(op, *args) -> str:
  args_str = ' '.join(args)

  if op != operator.ne:
    op_str = None
    if op == operator.add: op_str = '+'
    elif op == operator.sub: op_str = '-'
    elif op == operator.mul: op_str = '*'
    elif op == operator.truediv: op_str = '/'
    elif op == operator.eq: op_str = '='
    elif op == operator.and_: op_str = 'and'
    elif op == operator.or_: op_str = 'or'
    elif op == operator.gt: op_str = '>'
    elif op == operator.ge: op_str = '>='
    elif op == operator.lt: op_str = '<'
    elif op == operator.le: op_str = '<='
    else: raise TypeError('NYI: %s' % op)

    return '(%s %s)' % (op_str, args_str)
  else:
    return '(not (= %s))' % args_str

def unary_skfn(op, *args) -> str:
  if op == operator.neg: return '-%s' % args[0]
  else: raise TypeError('NYI: %s' % op)

def unary_rktfn(op, *args) -> str:
  if op == operator.neg: return '(- %s)' % args[0]
  elif op == operator.not_: return '(not %s)' % args[0]
  else: raise TypeError('NYI: %s' % op)

Program.stmt_types = [FnDecl]
FnDecl.stmt_types = [Block]
Block.stmt_types = [Assign, If, While, Return, Call]
BinaryOp.valid_ops = [operator.add, operator.sub, operator.mul, operator.truediv, operator.mod,
                      operator.and_, operator.or_,
                      operator.gt, operator.ge, operator.lt, operator.le, operator.eq, operator.ne]
BinaryOp.to_skfn = binary_skfn
BinaryOp.to_rktfn = binary_rktfn
UnaryOp.valid_ops = [operator.neg, operator.not_]
UnaryOp.to_skfn = unary_skfn
UnaryOp.to_rktfn = unary_rktfn
Var.valid_types = Lit.valid_types = [int, bool, Expr]
Expr.sktype_fn = sktype_fn


