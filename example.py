from metalift import ir
from metalift.synthesize_auto import synthesize

x = ir.Var("x", ir.Int())

correct = ir.And(
    ir.Ge(
        ir.Call('f', ir.Int(), x), # fn name, return type, arg
        ir.IntLit(0)
    ),
    ir.Ge(
        ir.Call('f', ir.Int(), x),
        x
    )
)

grammar = x # must not be recursive (i.e. constant depth)

for i in range(2):
    grammar = ir.Choose(
        ir.Add(grammar, grammar),
        ir.Sub(grammar, grammar),
        ir.Mul(grammar, grammar)
    ) # construct grammar (i.e. all possible functions)

synthF = ir.Synth(
    "f", # function name
    grammar, # possible bodies
    x
)

result = synthesize(
    "example", # name of the synthesis problem
    [], # util functions
    {x}, # vars to verify over
    [synthF], # functions to synthesize
    [], # predicates to verify
    correct, # verification condition
    [synthF], # type metadata for fns to synthesize if needed, or just the synth node
    unboundedInts=True
)

print(result)
