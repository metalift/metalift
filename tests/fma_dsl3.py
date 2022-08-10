import shutil
from typing import cast

from metalift.objects import Target, Int, MLObject
from metalift.ir import *
from metalift.transpiler import Transpiler

### Target language definition
# computes x + y * z
fma = Target("fma", [metalift.objects.Int, metalift.objects.Int, metalift.objects.Int], metalift.objects.Int,
             # name, arg types, return type
             lambda x, y, z: x + y * z,  # semantic def
             lambda a, b, c: f"fma({a.codegen()}, {b.codegen()}, {c.codegen()})")  # codegen fn

Lit.codegen = lambda self: self.val()
Var.codegen = lambda self: self.name()
Add.codegen = lambda self: f'{" + ".join([str(a.codegen()) for a in self.args])}'
Int.codegen = lambda self: f"{self.src.codegen()}"
FnDecl.codegen = lambda self: f'def {self.name()}({", ".join([str(a.codegen()) for a in self.arguments()])}):\n  ' \
                              f'return {self.body().codegen()}'


### Grammar definition
# start = fma(v, v, v) + fma(v, v, v)
# v = v+v (rec. depth 1) | var | 0

# version 1: no non terminal, recursion computed programmatically
def grammar_prog(readVars: typing.List[Int], retVal: Int, isLoop: bool) -> Dict[MLObject, MLObject]:
    def vars(depth: int, *vs: Int) -> Int:
        if depth == 0:
            return choose(*vs, Int(0))
        else:
            return choose(vars(depth - 1, *vs) + vars(depth - 1, *vs), *vs, Int(0))

    return {retVal: cast(Int, fma.call(vars(1, *readVars), vars(1, *readVars), vars(1, *readVars))) +
                    cast(Int, fma.call(vars(1, *readVars), vars(1, *readVars), vars(1, *readVars)))}


# version 2: using a non terminal with recursion inlined - not supported yet
# def grammar_nonterm(readVars: typing.List[Int], retVal: Int, isLoop: bool) -> Dict[MLObject, MLObject]:
#     vars = Int(Var(Int, "nonTerm"))
#     return {vars: choose(choose(*readVars, IntLit(0)) + choose(*readVars, IntLit(0)), *readVars, Int(0)),
#             retVal: fma.call(vars, vars, vars)}

# version 3: using a non terminal with non-programmatic recursion - not supported yet
# def grammar_recursive(readVars: typing.List[Int], retVal: Int, isLoop: bool) -> Dict[MLObject, MLObject]:
#     vars = Int(Var(Int, "nonTerm"))
#     return {vars: choose(recurse(vars, 1) + recurse(vars, 1), *readVars, Int(0)), # recurse(<non terminal>, <levels>)
#             rv: choose(*readVars, fma.call(vars, vars, vars))}


if __name__ == "__main__":
    t = Transpiler(grammar_prog, cvcPath=shutil.which("cvc5"))
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
    print("code is %s" % code)
    exec(code)
