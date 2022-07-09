from metalift.ir import *
from metalift.transpiler import Transpiler

### Target language definition
# computes x + y * z
fma = Target("fma", [Int(), Int(), Int()], Int(),  # name, arg types, return type
             lambda x,y,z: Add(x, Mul(y, z)),      # semantic def
             lambda a,b,c: f"fma({a.codegen()}, {b.codegen()}, {c.codegen()})")  # codegen fn

Lit.codegen = lambda self: self.val()
Var.codegen = lambda self: self.name()
Add.codegen = lambda self: f'{" + ".join([str(a.codegen()) for a in self.args])}'
FnDecl.codegen = lambda self: f'def {self.name()}({", ".join([str(a.codegen()) for a in self.arguments()])}):\n  ' \
                              f'return {self.body().codegen()}'

### Grammar definition
# start = fma(v, v, v) + fma(v, v, v)
# v = v+v (rec. depth 1) | var | 0

# no non terminal, recursion computed programmatically
def grammar_prog(readVars: typing.List[Var], retVal: Var, isLoop: bool) -> Dict[NonTerm, Expr]:
    def vars(depth: int, *readVars: Var) -> Choose:
        if depth == 0:
            return Choose(*readVars, IntLit(0))
        else:
            return Choose(Add(vars(depth - 1, *readVars), vars(depth - 1, *readVars)), *readVars, IntLit(0))

    rv = NonTerm(Int(), isStart=True)
    return {rv: Add(fma.call(vars(1, *readVars), vars(1, *readVars), vars(1, *readVars)),
                    fma.call(vars(1, *readVars), vars(1, *readVars), vars(1, *readVars)))}

# using a non terminal with recursion inlined - not supported yet
# def grammar_nonterm(readVars: typing.List[Var], retVal: Var, isLoop: bool) -> Dict[NonTerm, Expr]:
#     rv = NonTerm(Int(), isStart=True)
#     vars = NonTerm(Int())
#     return {vars: Choose(Add(Choose(*readVars, IntLit(0)), Choose(*readVars, IntLit(0))), *readVars, IntLit(0)),
#             rv: fma.call(vars, vars, vars)}

# using a non terminal with non-programmatic recursion - not supported yet
# def grammar_recursive(readVars: typing.List[Var], retVal: Var, isLoop: bool) -> Dict[NonTerm, Expr]:
#     rv = NonTerm(Int(), isStart=True)
#     vars = NonTerm(Int())
#     return {vars: Choose(Add(rec(vars, 1), rec(vars, 1)), *readVars, IntLit(0)), # rec = max recursive depth
#             rv: Choose(*readVars, fma.call(vars, vars, vars))}


if __name__ == "__main__":
    t = Transpiler(grammar_prog, cvcPath="cvc5")
    r = t.transpile("fma_dsl.ll", "test")  # loops file defaults to replacing ".ll" to ".loops" in first arg

    print(f"transpiled: {r.codegen()}")

    # let's put the transpiled code with the actual definition of fma and run it
    code = \
"""
def fma(x, y, z): 
  return x + y * z 
      
""" + \
      \
r.codegen() + \
      \
"""
print(test(1,2,3,4))  # 2 * ((1 + 3) + 2 * 4) = 24
"""

    exec(code)
