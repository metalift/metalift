import collections
import operator
from enum import Enum
import typing

## metalift IR. There are two base classes: Exprs return a typed value,
## and Stmts do not return anything. The language is supposed to be typed, although
## we haven't implemented type inference yet.

### Expressions ###

class Expr:
  sktype_fn = None
  rkttype_fn = None
  z3type_fn = None

  def __init__(self, *args):
    self.args = args


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

    if op == operator.add or op == operator.sub or op == operator.mul or op == operator.truediv:
      self.type = int
    elif op == operator.eq or op == operator.and_ or op == operator.or_ or op == operator.gt or op == operator.ge or \
         op == operator.lt or op == operator.le:
      self.type = bool
    else:
      self.type = None

  def __repr__(self):
    return '%s(%s)' % (self.op, ', '.join(str(x) for x in self.args))

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.op == other.op and self.args == other.args

  def __hash__(self):
    return hash((self.op, self.args))


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
    self.type = None  # need type inference

  def __repr__(self):
    return '%s(%s)' % (self.name, ', '.join(str(x) for x in self.args))

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.name == other.name and self.args == other.args

  def __hash__(self):
    return hash((self.name, self.args, self.type))


# ignore this for now
# def gen_Expr(name, types, ops):
#   def init(self, op, *args):
#     Expr.__init__(self, op, args)
#     for a in args:
#       if not isinstance(a, self.valid_types):
#         raise TypeError('only supported types are: ' + str(self.valid_types))
#
#     if not any(op == o for o in self.valid_ops):
#       raise TypeError('only supported ops are: ' + str(self.valid_ops))
#
#   return type(name, (Expr, ), {'__init__': init, 'valid_types': types, 'valid_ops': ops})


class Var(Expr):
  def __init__(self, name, t):
    # hack according to https://bugs.python.org/issue34568
    if hasattr(t, '__origin__'):
      t = t.__origin__
    if not any(issubclass(t, vt) for vt in Var.valid_types):
      raise TypeError('only supported vars of type: %s and not %s' % (Var.valid_types, t))
    self.name = name
    self.type = t

  def __repr__(self):
    return '%s:%s' % (self.name, self.type.__name__)

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.name == other.name and self.type == other.type

  def __hash__(self):
    return hash((self.name, str(self.type)))


class Lit(Expr):
  valid_types = []

  def __init__(self, val, t):
    self.val = val
    if not any(isinstance(val, ty) for ty in Lit.valid_types):
      raise TypeError('only supported types are: %s but not %s' % (str(Lit.valid_types), str(val)))
    self.type = t

  def __repr__(self):
    return '%s:%s' % (str(self.val), self.type.__name__)

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.type == other.type and self.val == other.val

  def __hash__(self):
    return hash(self.val)


class Field(Expr):
  def __init__(self, target, name):
    super().__init__()
    self.target = target
    self.name = name
    self.type = None  # XXX

  def __repr__(self):
    return '%s.%s' % (self.target, self.name)

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.target == other.target and self.name == other.name \
           and self.type == other.type

# def gen_Lit(name, types):
#
#   def init(self, val):
#     Lit.__init__(self, val, None)
#     if not isinstance(val, self.valid_types):
#       raise TypeError('only supported types are: ' + str(self.valid_types))
#
#   return type(name, (Lit,), {'__init__': init, 'valid_types': types})


# python specific expression
class Unpack(Expr):
  def __init__(self, val):
    self.val = val

  def __repr__(self):
    return 'unpack(%s)' % str(self.val)

# list operations
class ListConstructor(Expr):
  def __init__(self, *exprs: Expr):
    super().__init__(*exprs)
    self.exprs = exprs
    #self.type = List[exprs[0].type] if len(exprs) > 0 else None  # need type inference
    self.type = typing.List[int]

  def __repr__(self):
    return 'List(%s)' % ", ".join([repr(e) for e in self.args])

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.args == other.args and self.type == other.type


class ListAccess(Expr):  # l[e]
  def __init__(self, target, index, type_):
    super().__init__()
    self.target = target
    self.index = index
    self.type = type_

  def __repr__(self):
    return '%s[%s]' % (self.target, self.index)

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.target == other.target and self.index == other.index \
           and self.type == other.type

  def __hash__(self):
    return hash((self.target, self.index, self.type))


# non deterministic execution -- only used for synthesis
class Choose(Expr):
  def __init__(self, *args):
    super().__init__(*args)
    self.args = args
    types = {a.type for a in args}
    if len(types) != 1:  # need to check for subtypes
      raise TypeError('not all arguments are of the same type: %s: %s' % (str(self.args), str([a.type for a in self.args])))
    self.type = types.pop()

  def __repr__(self):
    return 'choose(%s)' % ', '.join(str(x) for x in self.args)

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.args == other.args


### Statements ###
class Stmt:
  def __init__(self, *args):
    self.args = args

class Assign(Stmt):
  def __init__(self, left, right):
    super().__init__(left, right)
    self.left = left
    self.right = right
    if not (isinstance(left, Var) or isinstance(left, ListAccess)):
      raise TypeError('left hand side of assign must be a Var rather than %s' % left)

  def __repr__(self):
    return '%s = %s;\n' % (self.left, self.right)


class If(Stmt):
  def __init__(self, cond, conseq, alt = None):
    super().__init__(cond, conseq, alt)
    self.type = None
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
    self.cond = cond
    if len(body) == 1 and isinstance(body[0], Block):
      super().__init__(cond, body)
      self.body = body
    else:
      super().__init__(cond, Block(*body))  # block also expects a variable number of arguments
      self.body = Block(*body)

  def __repr__(self):
    return 'while (%s) { %s }' % (self.cond, self.body)


class Return(Stmt):
  def __init__(self, body):
    super().__init__(body)
    self.body = body

  def __repr__(self):
    return 'return %s;' % self.args[0]


class Branch(Stmt):  # continue or break
  class Type(Enum):
    Continue = 1
    Break = 2

  def __init__(self, type):
    super().__init__(None)
    self.type = type

  def __repr__(self):
    return 'continue;' if self.type == Branch.Type.Continue else 'break;'


class Block(Stmt):
  stmt_types = []

  def __init__(self, *stmts):
    stmts = list(stmts)
    super().__init__(*stmts)
    self.stmts = stmts
    for s in stmts:
      if not any(isinstance(s, t) for t in Block.stmt_types):
        raise TypeError('Block body needs to be a %s rather than %s: %s' % (Block.stmt_types, type(s), s))

  def __repr__(self):
    return '{ %s }' % ('\n'.join(repr(s) for s in self.stmts))


class FnDecl(Stmt):
  stmt_types = []

  def __init__(self, name: str, args: typing.List[Var], rtype: type, body: Block):
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


# an ExprStmt is a single function call that has no return value
class ExprStmt(Stmt):
  def __init__(self, e: Expr):
    super().__init__(e)
    self.expr = e

  def __repr__(self):
    return '(%s)' % self.expr


# the following stmts are only used to express the proof obligations to be sent to the solvers.
# they are not intended to be used in the input or the target language
class Assert(Stmt):
  def __init__(self, e: Expr):
    super().__init__(e)
    self.expr = e

  def __repr__(self):
    return 'assert(%s)' % self.expr


class Assume(Stmt):
  def __init__(self, e: Expr):
    super().__init__(e)
    self.expr = e

  def __repr__(self):
    return 'assume(%s)' % self.expr


class Havoc(Stmt):
  def __init__(self, *args):
    super().__init__(*args)
    self.args = args

  def __repr__(self):
    return 'havoc(%s)' % ', '.join(str(x) for x in self.args)

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.args == other.args


class Forall(Stmt):
  def __init__(self, vars, expr):
    super().__init__(expr)
    self.vars = vars
    self.expr = expr

  def __repr__(self):
    return 'forall(%s, %s)' % (', '.join(str(x) for x in self.vars), self.expr)

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.vars == other.vars and self.expr == other.expr


class Program:
  stmt_types = []

  def __init__(self, imports, stmts):
    self.imports = imports
    self.fns = {}
    self.stmts = stmts
    self.user_axioms = []
    for s in stmts:
      #if not any(isinstance(s, t) for t in Program.stmt_types):
      #  raise TypeError('only supported types are: %s but not %s' % (self.stmt_types, s))
      if isinstance(s, FnDecl):
        self.fns[s.name] = s

  def __repr__(self):
    axioms = '\n'.join(str(a) for a in self.user_axioms)
    stmts = '\n'.join(str(s) for s in self.stmts)
    return f"### user axioms ### \n{axioms} \n### stmts ### \n{stmts}"


# ignore this for now
# def gen_Stmt(name, types, repr_fn):
#   def init(self, *args):
#     Stmt.__init__(self, args)
#     for a in args:
#       if not isinstance(a, self.valid_types):
#         raise TypeError('only supported types are: %s' % self.valid_types)
#
#   return type(name, (Stmt, ), {'__init__': init, 'valid_types': types, '__repr__': repr_fn})


## the following funtions maps the types between the Metalift IR and Sketch, Racket (Rosette), and Z3

def sktype_fn(t: type) -> str:
  if t == int: return 'int'
  elif t == bool: return 'bit'
  else: raise TypeError('NYI: %s' % t)

def rkttype_fn(t: type) -> str:
  if t == int: return 'integer?'
  elif t == bool: return 'boolean?'
  else: raise TypeError('NYI: %s' % t)

def z3type_fn(t: type) -> str:
  if t == int: return 'Int'
  elif t == bool: return 'Bool'
  elif t == list or t == typing.List[int]: return '(MLList Int)'
  elif t == collections.abc.Callable: return 'Int'
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
    if op == operator.add: op_str = '+'
    elif op == operator.sub: op_str = '-'
    elif op == operator.mul: op_str = '*'
    elif op == operator.truediv: op_str = '/'
    elif op == operator.eq: op_str = 'eq?'
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

def binary_z3fn(op, *args) -> str:
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

def unary_z3fn(op, *args) -> str:
  if op == operator.neg: return '-%s' % args[0]
  else: raise TypeError('NYI: %s' % op)


## the following defines the valid IR types allowed in the spec, in anticipation that we will
## create different 'dialects' to accommodate different input languages (Java, C, Python, etc)
Program.stmt_types = [FnDecl]
FnDecl.stmt_types = [Block]
Block.stmt_types = [Assign, If, While, Return, Call, ExprStmt, Branch, Assert, Assume, Havoc, Block, Var]
BinaryOp.valid_ops = [operator.add, operator.sub, operator.mul, operator.truediv, operator.mod,
                      operator.and_, operator.or_,
                      operator.gt, operator.ge, operator.lt, operator.le, operator.eq, operator.ne]
BinaryOp.to_skfn = binary_skfn
BinaryOp.to_rktfn = binary_rktfn
BinaryOp.to_z3fn = binary_z3fn
UnaryOp.valid_ops = [operator.neg, operator.not_]
UnaryOp.to_skfn = unary_skfn
UnaryOp.to_rktfn = unary_rktfn

Var.valid_types = [bool, int, float, typing.List, Expr, typing.Callable]
Lit.valid_types = [bool, int, float, Expr]

## shortcuts
true_lit = Lit(True, bool)
false_lit = Lit(False, bool)

def true(): return true_lit
def false(): return false_lit
def num(n: int): return Lit(n, int)

Expr.sktype_fn = sktype_fn
Expr.rkttype_fn = rkttype_fn
Expr.z3type_fn = z3type_fn

def implies(cond, conseq):
  return BinaryOp(operator.or_, UnaryOp(operator.not_, cond), conseq)
