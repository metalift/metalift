from metalift.ir import Var, FnDecl, FnDeclNonRecursive, Choose, Synth
from metalift.ir import Add, Mul, Eq, Call, Lit, IntLit
from metalift.ir import Int
from metalift.analysis import analyze
from metalift.synthesize_auto import synthesize

# Specifies the lang we want to compile to
def targetLang():
    x = Var("x", Int()) # variables to be used in semantic function definition
    y = Var("y", Int())
    z = Var("z", Int())
    fma = FnDeclNonRecursive("fma",             # function name
                             Int(),             # return type
                             Add(x, Mul(y, z)), # body of the function
                             x, y, z)           # function inputs
    return [fma]

# Grammar - specifies the language (space of programs) we want to consider as possible transpiled code (i.e. outputs)
# specification is restricted to: metalift IR, semantic fns we define
#
# For now, let's consider outputs that are additions of input vars or the result of calling fma
def grammar(ci):
  name = ci.name

  inputVars = Choose(*ci.readVars, IntLit(0))
  var_or_add = Add(inputVars, inputVars)
  var_or_fma = Choose(
    *ci.readVars, Call("fma", Int(), var_or_add, var_or_add, var_or_add)
  )
  
  rv = ci.modifiedVars[0]
  # all writes should be computed using the grammar above. I.e., written_var = var_or_fma + var_or_fma 
  summary = Eq(rv, Add(var_or_fma, var_or_fma))

  return Synth(name,                            # name of the function we are transpiling
               summary,                         # grammar defined above
               *ci.modifiedVars, *ci.readVars)  # list of input and output variables

#basename = "fma"
#filename = "tests/fma_dsl.ll"
#fnName = "test"
#loopsFile = "tests/fma_dsl.loops"
basename = "fma"
filename = "fma.ll"
fnName = "test"
loopsFile = "fma.loops"
cvcPath = "cvc5"
(vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

print("====== grammar")
invAndPs = [grammar(ci) for ci in loopAndPsInfo]

lang = targetLang()

candidates = synthesize(basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath)

def codeGen(summary: FnDecl):
  expr = summary.body() 
  def eval(expr):
    if isinstance(expr, Eq):
      return f"{expr.e1()} = {eval(expr.e2())}"
    elif isinstance(expr, Add):
      return f"{eval(expr.args[0])} + {eval(expr.args[1])}"
    elif isinstance(expr, Call):
      eval_args = []
      for a in expr.arguments():
        eval_args.append(eval(a))
      return f"{expr.name()}({', '.join(eval_args)})"
    elif isinstance(expr, Lit):
      return str(expr.val())
    else:
      return str(expr)
  return eval(expr)

summary = codeGen(candidates[0])

print(summary)
