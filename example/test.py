# metalift input code
def vctest(n: int) -> int:
  sum: int = 0
  i: int = 0

  # invariant: sum = my_sum(i)
  while i < n:
    sum = sum + 1
    i = i + 1

  # postcondition: sum = my_sum(n)
  return sum

#print('sum: %s' % vctest(20))


# old code below
#
# def rec1(vars: List[ir.Var], depth: int) -> int:
#   #op: ir.Choose = Choose(operator.add, operator.sub)
#
#   #op = ir.Choose(operator.add, operator.sub)
#   if depth == 0:
#     return ir.BinaryOp(operator.add, ir.Choose(*vars), ir.Choose(*vars))
#   else:
#     return ir.BinaryOp(operator.add, rec1(vars, depth - 1), rec1(vars, depth - 1))
#   #return ir.Choose(ir.BinaryOp(operator.add, v1, v2), ir.BinaryOp(operator.sub, v1, v2))
#   #return op
#
#
# def rec2(vars, depth):
#   #op = ir.Choose(operator.add, operator.sub)
#   if depth == 0:
#     return ir.BinaryOp(operator.add, ir.Choose(*vars), ir.Choose(*vars))
#   else:  # return an ML AST
#     cond = ir.Choose(ir.Lit(True, bool), ir.Lit(False, bool))
#     cons = ir.Return(rec2(vars, 0))
#     alt = ir.Return(ir.BinaryOp(operator.add, rec2(vars, depth - 1), rec2(vars, depth - 1)))
#     return ir.If(cond, cons, alt)
#
# def rec3(vars, depth):
#   op = ir.Choose(ir.Field('operator', 'add'), ir.Field('operator', 'sub'))
#   if depth == 0:
#     return ir.Choose(*vars)
#   else:
#     v = ir.Choose(ir.Lit(True, bool), ir.Lit(False, bool))
#     return ir.If(v, rec3(vars, 0), ir.BinaryOp(op, rec3(vars, depth - 1), rec3(vars, depth - 1)))


# def rec1(vars, depth):
#   op = ir.Choose(operator.add, operator.sub)
#   if depth == 0:
#     return ir.BinaryOp(op, ir.Choose(*vars), ir.Choose(*vars))
#   else:
#     return ir.BinaryOp(op, rec1(vars, depth - 1), rec1(vars, depth - 1))
