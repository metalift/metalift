from typing import List
from metalift.ir import fn_decl, fn_decl_recursive, choose, Synth
from metalift.ir import call, Lit, IntLit, Add, Call, Eq, Expr, Ite, Lit, Sub, TupleExpr
from metalift.ir import Int, Bool, Object
from metalift.frontend.llvm import Driver
from metalift.synthesize_auto import synthesize

def targetLang():
  x = Int("x") # variables to be used in semantic function definition
  y = Int("y")
  z = Int("z")
  fma = fn_decl("fma",             # function name
               Int,             # return type
               x + y * z, # body of the function
               x, y, z)           # function inputs
  return [fma]

def grammar(writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool) -> Bool:
    ret_val = writes[0]
    var = choose(*reads, Int(0))
    added = var + var
    fma_call_object = call("fma", Int, added, added, added)
    var_or_fma = choose(*reads, fma_call_object)
    # all writes should be computed using the grammar above. I.e., written_var = var_or_fma + var_or_fma. and the return value must be equal to it
    return ret_val == var_or_fma + var_or_fma

filename = "/Users/taeyoungkim/metalift/custom_test/fma.ll"
basename = "test"

fnName = "test"
loopsFile = "/Users/taeyoungkim/metalift/custom_test/fma.loops"
cvcPath = "cvc5"

driver = Driver()
test = driver.analyze(
    llvm_filepath=filename,
    loops_filepath=loopsFile,
    fn_name=fnName,
    target_lang_fn=targetLang,
    inv_grammars=None,
    ps_grammar=grammar
)


base = Int("base")
arg1 = Int("arg1")
base2 = Int("base2")
arg2 = Int("arg2")
driver.add_var_objects([base, arg1, base2, arg2])

test(base, arg1, base2, arg2)

driver.synthesize(filename="fma")

def codeGen(expr: Expr) -> str:
    def eval(expr: Expr) -> str:
        if isinstance(expr, Eq):
            return f"{expr.e1()} == {eval(expr.e2())}"
        if isinstance(expr, Add):
            return f"{eval(expr.args[0])} + {eval(expr.args[1])}"
        if isinstance(expr, Sub):
            return f"{eval(expr.args[0])} - {eval(expr.args[1])}"
        if isinstance(expr, Call):
            eval_args = []
            for a in expr.arguments():
                eval_args.append(eval(a))
            return f"{expr.name()}({', '.join(a for a in eval_args)})"
        if isinstance(expr, Lit):
            return f"{expr.val()}"
        if isinstance(expr, TupleExpr):
            return f"({', '.join(eval(a) for a in expr.args)})"
        if isinstance(expr, Ite):
            return f"{eval(expr.e1())} if {eval(expr.c())} else {eval(expr.e2())}"
        else:
            return "%s"%(expr)
    return eval(expr)

summary = test.codegen(codeGen)

print(summary)
