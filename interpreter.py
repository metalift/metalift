from frontend import python
from state import State
import ir
import ast
import operator
import functools
import inspect

class SearchGrammar:
  debug = False
  cache = {}

  def __init__(self, func):
    functools.update_wrapper(self, func)
    self.func = func

  def __call__(self, *args, **kwargs):
    if self.debug:
      print(f"Called {self.func.__name__!r} " + str(args))

    # Get source of function, parse it to an AST
    tree = ast.parse(inspect.getsource(self.func))

    # Unwrap the AST to get function declaration
    fnDecl = tree.body[0]

    # Run interpreter on fnDecl for current set of arguments
    i = Interpreter(*args).visit(fnDecl)

    if self.debug:
      print(i)

    # Return the interpreted function
    return i


class Interpreter(ast.NodeTransformer):
  debug = False

  # Constructor
  def __init__(self, *args):
    self.eval = True
    self.args = args
    self.state = State()

  def generic_visit(self, node):
    raise TypeError('NYI:', node)

  def parseToIR(self, expr):
    return python.Translator().visit(ast.parse(str(expr)).body[0])  # TODO: See if there is a less hacky way of doing this

  # Interpret function declaration
  def visit_FunctionDef(self, n):
    # Create a new frame to hold the function's local scope
    self.state.newFrame()

    for i in range(len(n.args.args)):
      param = n.args.args[i]
      arg = self.args[i]
      self.state.evaluatesTo(param.arg, arg)

    for stmt in n.body:
      if not self.visit(stmt):
        break

    # Pop frame
    frame = self.state.pop()

    return frame.rv

  # Interpret return statement
  def visit_Return(self, n):
    r = self.visit(n.value)
    self.state.retVal(r)
    return False

  # Interpret assignment statement
  def visit_Assign(self, n):
    if len(n.targets) > 1:
      raise TypeError('multi-assign NYI: %s' % n)

    self.eval = False
    target = self.visit(n.targets[0])
    self.eval = True

    val = self.visit(n.value)
    if len(n.targets) > 1:
      raise TypeError('multi-assign NYI: %s' % n)

    self.state.evaluatesTo(target, val)
    return True

  # Interpret list comprehension
  def visit_ListComp(self, n):
    expr = n.elt
    gens = n.generators

    # Can be done with a recursive implementation (i think)
    if len(gens) > 1:
      raise TypeError("NYI: multi-generator list comprehensions.", ast.dump(n))

    if len(gens[0].ifs) > 1:
      raise TypeError("NYI: multi-filter list comprehensions.", ast.dump(n))

    target = gens[0].target.id
    iter = self.visit(gens[0].iter)
    filter = gens[0].ifs[0]

    self.state.dupFrame()
    res = []
    for val in iter:
      self.state.evaluatesTo(target, val)         # update local scope
      cond = self.visit(filter)                   # interpret filter condition in local scope
      expr_eval = self.visit(expr)                # interpret expression in local scope
      if cond:
        res.append(expr_eval)
    self.state.pop()

    return res

  # Interpret conditionals
  def visit_If(self, n):
    test = self.visit(n.test)

    if not isinstance(test, ir.Expr):
      if test:
        self.state.dupFrame()
        for stmt in n.body:
          if not self.visit(stmt):
            break
        cons = self.state.pop()

        if cons.rv:
          self.state.retVal(cons.rv)
          return False
        else:
          self.state.update(cons)
      else:
        self.state.dupFrame()
        for stmt in n.orelse:
          if not self.visit(stmt):
            break
        altr = self.state.pop()

        if altr.rv:
          self.state.retVal(altr.rv)
          return False
        else:
          self.state.update(altr)
    else:
      self.state.dupFrame()
      for stmt in n.body:
        if not self.visit(stmt):
          break
      cons = self.state.pop()

      self.state.dupFrame()
      for stmt in n.orelse:
        if not self.visit(stmt):
          break
      altr = self.state.pop()

      if cons.rv and altr.rv:
        self.state.retVal(ir.If(test, cons.rv, altr.rv))
        return False
      elif not cons.rv and not altr.rv:
        self.state.merge(test, cons, altr)
        return True
      else:
        raise TypeError("NYI")

    return True

  # Interpret binary operator expression
  def visit_BinOp(self, n):
    lop = self.visit(n.left)
    rop = self.visit(n.right)

    # If either operand is symbolic, the output is also symbolic
    if isinstance(lop, ir.Expr) or isinstance(rop, ir.Expr):
      lop = lop if isinstance(lop, ir.Expr) else self.parseToIR(lop)
      rop = rop if isinstance(rop, ir.Expr) else self.parseToIR(rop)
      if isinstance(n.op, ast.Add): return ir.BinaryOp(operator.add, lop, rop)
      elif isinstance(n.op, ast.Sub): return ir.BinaryOp(operator.sub, lop, rop)
      elif isinstance(n.op, ast.Mult): return ir.BinaryOp(operator.mul, lop, rop)
      elif isinstance(n.op, ast.Div): return ir.BinaryOp(operator.floordiv, lop, rop)   # TODO: Double check which div to use
      else: raise TypeError('NYI:', n.op)
    else:
      if isinstance(n.op, ast.Add): return operator.add(lop, rop)
      elif isinstance(n.op, ast.Sub): return operator.sub(lop, rop)
      elif isinstance(n.op, ast.Mult): return operator.mul(lop, rop)
      elif isinstance(n.op, ast.Div): return operator.floordiv(lop, rop)                  # TODO: Double check which div to use
      else: raise TypeError('NYI; %s' % n.op)

  # Interpret comparison expressions
  def visit_Compare(self, n):
    if len(n.ops) > 1: raise TypeError('NYI: %s' % n.ops)
    if len(n.comparators) > 1: raise TypeError('NYI: %s' % n.comparators)

    lop = self.visit(n.left)
    rop = self.visit(n.comparators[0])

    # If either operand is symbolic, the output is also symbolic
    if isinstance(lop, ir.Expr) or isinstance(rop, ir.Expr):
      lop = lop if isinstance(lop, ir.Expr) else self.parseToIR(lop)
      rop = rop if isinstance(rop, ir.Expr) else self.parseToIR(rop)
      op = n.ops[0]
      if isinstance(op, ast.Eq): return ir.BinaryOp(operator.eq, lop, rop)
      elif isinstance(op, ast.Lt): return ir.BinaryOp(operator.lt, lop, rop)
      elif isinstance(op, ast.Gt): return ir.BinaryOp(operator.gt, lop, rop)
      elif isinstance(op, ast.LtE): return ir.BinaryOp(operator.le, lop, rop)
      elif isinstance(op, ast.GtE): return ir.BinaryOp(operator.ge, lop, rop)
      elif isinstance(op, ast.NotEq): return ir.BinaryOp(operator.ne, lop, rop)
      else: raise TypeError('NYI:', n.op)
    else:
      op = n.ops[0]
      if isinstance(op, ast.Eq): return operator.eq(lop, rop)
      elif isinstance(op, ast.Lt): return operator.lt(lop, rop)
      elif isinstance(op, ast.Gt): return operator.gt(lop, rop)
      elif isinstance(op, ast.LtE): return operator.lte(lop, rop)
      elif isinstance(op, ast.GtE): return operator.gte(lop, rop)
      elif isinstance(op, ast.NotEq): return operator.ne(lop, rop)
      else: raise TypeError('NYI: %s' % str(op))

  # Interpret function call
  def visit_Call(self, n):
    fn = self.visit(n.func)
    args_eval = []
    for arg in n.args:
      if not isinstance(arg, ast.Starred):
        args_eval.append(self.visit(arg))
      else:
        expr = self.visit(arg.value)
        if isinstance(expr, ir.Expr):
          raise TypeError("Cannot star a symbolic variable, not supported in the IR:", expr)
        else:
          if type(expr) is list or type(expr) is tuple:
            args_eval += [self.visit(v) for v in expr]
          else:
            raise TypeError("Cannot star non list/tuple type:", expr)

    # Special handling for Choose function
    if fn == "Choose":
      parsed_args = [arg if isinstance(arg, ir.Expr) else self.parseToIR(arg) for arg in args_eval]
      return ir.Choose(*parsed_args)

    if not n.func.id in globals()["__builtins__"]:
      raise TypeError("NYI: Only built-in methods allowed (" + n.func.id + ")")

    #func = globals()["__builtins__"][n.func.id]
    #args_eval = [self.visit()]

    raise TypeError("NYI: Function calls ('" + n.func.id + "')")

  # Interpret field access
  def visit_Attribute(self, n):
    container = self.visit(n.value)

    # If symbolic var, return symbolic AST expr
    if isinstance(container, ir.Expr):
      # Edge case: We can evaluate types of symbolic variables even
      # though we don't know their values
      if n.attr == "type":
        return container.type.__name__
      else:
        return ir.Field(container, n.attr)
    # If concrete expr, evaluate it
    else:
      raise TypeError("NYI")

  # Interpret variable names
  def visit_Name(self, n):
    if self.eval and self.state.contains(n.id):
      return self.state.evaluate(n.id)
    else:
      return n.id

  # Interpret ir.Var (special handling)
  @staticmethod
  def visit_Var(n):
    return n

  # Interpret all constants (Python 3.8+)
  def visit_Constant(self, n):
    return n.n

  # def resolve(self, v, is_var=True):
  #   if isinstance(v, ir.Lit):
  #     return v
  #   else:
  #     raise TypeError('NYI: %s' % v)

  # Interpret program
  # def visit_Program(self, n):
  #   raise TypeError('Interpreter called on ir.Program. Only supported for ir.FnDecl.')
  #
  #
  # # Interpret code block
  # def visit_Block(self, n):
  #   returned = False
  #   for s in n.stmts:
  #     if not self.visit(s):
  #       returned = True
  #       break
  #   return returned
  #
  # def visit_Return(self, n):
  #   r = self.visit(n.body)
  #   if isinstance(r, ir.Var):
  #     self.state.rv = self.state.var[r]
  #   else:
  #     self.state.rv = r
  #   return False
  #
  # # Interpret assignment statement
  # def visit_Assign(self, n):
  #   if not isinstance(n.left, ir.Var):
  #     raise TypeError('NYI')
  #
  #   self.state.var[n.left] = self.visit(n.right)
  #   return True
  #
  # # Interpret binary operators
  # def visit_BinaryOp(self, n):
  #   if self.debug:
  #     print("n is %s" % n)
  #
  #   return ir.BinaryOp(n.op, *[self.visit(a) for a in n.args])
  #
  # # Interpret unary operators
  # def visit_UnaryOp(self, n):
  #   return ir.UnaryOp(n.op, *[self.state.var[self.visit(a)] for a in n.args])
  #
  # # Interpret literal
  # @staticmethod
  # def visit_Lit(n):
  #   return n
  #
  # # Interpret variable
  # def visit_Var(self, n):
  #   return self.state.var[n]
  #
  # # TODO: Interpret function calls
  # def visit_Call(self, n):
  #   raise TypeError('NYI')
  #
  # # TODO: Interpret choose operator
  # def visit_Choose(self, n):
  #   raise TypeError('NYI')
  #
# def visit_Field(self, n):
#   if n.target == 'operator' and n.name == 'add':
#     return '+'
#   elif n.target == 'operator' and n.name == 'sub':
#     return '-'
#   else:
#     raise TypeError('NYI: %s' % self)

# def visit_If(self, n: ir.If):
#   cond = self.visit(n.cond)
#   s = copy.deepcopy(self.state)
#
#   cons_cont = self.visit(n.conseq)
#   cons_state = copy.deepcopy(self.state)
#
#   self.state = s
#   alt_cont = self.visit(n.alt)
#   alt_state = self.state
#
#   merged_state = Interpreter.State()
#   # merge
#   for v, cons_val in cons_state.var.items():
#     alt_val = alt_state.var[v]
#     if alt_val != cons_val:
#       print("%s is diff: %s and %s" % (v, cons_val, alt_val))
#       merged_state.var[v] = ir.If(cond, cons_val, alt_val)
#     else:
#       print("%s is same: %s and %s" % (v, cons_val, alt_val))
#       merged_state.var[v] = cons_val
#
#   if alt_state.rv != cons_state.rv:
#     merged_state.rv = ir.If(cond, cons_state.rv, alt_state.rv)
#   else:
#     merged_state.rv = cons_state.rv
#
#   self.state = merged_state
#   return True

#   # loop, while
#   def visit_While(self, n):
#     # create a new invariant function
#     inv_vars = list(self.state.var.keys())
#     inv = ir.FnDecl('inv', inv_vars, bool, ir.Block())
#     self.state.fns.append(inv)
#
#     # add assertion: inv is initially true
#     inv_call = ir.Call('inv', *[self.state.var[arg] for arg in inv_vars])
#     self.state.asserts.append(ir.Assert(inv_call))
#
#     cond = self.visit(n.cond)
#     # create new visitor for the body
#     body_visitor = VCGen()
#     for v in inv_vars:
#       body_visitor.state.var[v] = ir.Var(v.name, v.type)
#     body_cont = body_visitor.visit(n.body)
#     print("body: %s" % body_visitor.state)
#
#     # construct the assertion: cond & inv -> inv(body) => not(cond & inv) | inv(body)
#     inv_body_call = ir.Call('inv', *[body_visitor.state.var[arg] for arg in inv_vars])
#     inv_maintained = ir.BinaryOp(operator.or_, ir.UnaryOp(operator.not_, ir.BinaryOp(operator.and_, cond, inv_call)), inv_body_call)
#     self.state.asserts.append(ir.Assert(inv_maintained))
#
#     # add precond to current state: !cond & inv
#     self.state.precond.append(ir.BinaryOp(operator.and_, ir.UnaryOp(operator.not_, cond), inv_call))
#
#     return body_cont
#
#
# def translate_file(name):
#   with open(name, 'r') as source:
#     tree = ast.parse(source.read())
#     print(ast.dump(tree))
#     e = Translator()
#     v = e.visit(tree)
#     print('final state: %s' % e.vars)
#     return v
# t = python.translate_file('example/test.py')
# print('t: %s' % t)
#
    # op = n.ops[0]
    # if isinstance(op, ast.Eq): new_op = operator.eq
    # elif isinstance(op, ast.Lt): new_op = operator.lt
    # elif isinstance(op, ast.Gt): new_op = operator.gt
    # elif isinstance(op, ast.LtE): new_op = operator.le
    # elif isinstance(op, ast.GtE): new_op = operator.ge
    # elif isinstance(op, ast.NotEq): new_op = operator.ne
    # else: raise TypeError('NYI: %s' % str(op))
    #
    # return ir.BinaryOp(new_op, self.resolve(n.left), self.resolve(n.comparators[0]))