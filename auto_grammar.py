from ir import *

literals = {
  Int(): [
    # TODO(shadaj): seed from the program
    IntLit(i) for i in range(2)
  ],
  Bool(): [
    BoolLit(True),
    BoolLit(False)
  ],
}

expansions = {
  Int(): [
    lambda get: Add(get(Int()), get(Int())),
    lambda get: Sub(get(Int()), get(Int())),
    # lambda get: Mul(get(Int()), get(Int())),
  ],
  Bool(): [
    lambda get: And(get(Bool()), get(Bool())),
    lambda get: Or(get(Bool()), get(Bool())),
    lambda get: Not(get(Bool())),
    lambda get: Eq(get(Int()), get(Int())),
    lambda get: Lt(get(Int()), get(Int())),
    lambda get: Gt(get(Int()), get(Int())),
    # lambda get: Le(get(Int()), get(Int())),
    # lambda get: Ge(get(Int()), get(Int())),
  ]
}

def auto_grammar(out_type: Type, depth: int, *inputs: Union[Expr, ValueRef]) -> Expr:
  pool = {}
  for t, literal in literals.items():
    pool[t] = Choose(*literal)

  input_pool = {}
  for input in inputs:
    input_type = parseTypeRef(input.type)
    if input_type.name == "Tuple":
      for i, t in enumerate(input_type.args):
        if not t in input_pool:
          input_pool[t] = []
        input_pool[t].append(TupleSel(input, i))
    else:
      if not input_type in input_pool:
        input_pool[input_type] = []
      input_pool[input_type].append(input)
  
  for t, exprs in input_pool.items():
    pool[t] = Choose(pool[t], Choose(*exprs))
  
  for i in range(depth):
    next_pool = {}
    for t, expansion_list in expansions.items():
      new_elements = []
      for expansion in expansion_list:
        new_elements.append(expansion(lambda t: pool[t]))
      next_pool[t] = Choose(pool[t], Choose(*new_elements))

    pool = next_pool
  
  # for t in pool:
  #   if t != Bool():
  #     pool[t] = Choose(pool[t], Ite(
  #       pool[Bool()],
  #       pool[t],
  #       pool[t]
  #     ))

  return pool[out_type]
