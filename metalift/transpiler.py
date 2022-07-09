from typing import Union, Callable, List, Dict, cast

from llvmlite.binding import ValueRef

from metalift.analysis import analyze
from metalift.ir import Expr, Var, NonTerm, FnDecl, Target, Synth, Eq
from metalift.synthesize_auto import synthesize


class Transpiler:
  grammar: Callable[[List[Var], Var], Dict[NonTerm, Union[Expr, List[Expr]]]]
  cvcPath: str

  def __init__(self, grammar: Callable[[List[Var], Var, bool], Dict[NonTerm, Union[Expr, List[Expr]]]],
               cvcPath=None) -> None:
    self.grammar = grammar
    self.cvcPath = cvcPath

  def expand(self, name, readVars, modifiedVars, grammar):
    return Synth(name, Eq(modifiedVars[0], list(grammar.values())[0]), *modifiedVars, *readVars)

  def transpile(self, filename: str, fnName: str, loopsFile: str = None) -> Expr:
    if not loopsFile:
      if filename.endswith(".ll"):
        loopsFile = filename[:-2] + "loops"

    print(f"======= input: {filename}, fn: {fnName}, loops: {loopsFile}")
    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== generating grammar")

    basename = fnName

    invAndPs = [self.expand(basename, ci.readVars, ci.modifiedVars,
                            self.grammar(ci.readVars, ci.modifiedVars[0], ci.name.startswith("inv")))
                for ci in loopAndPsInfo]

    lang = list(Target.definedFns.values())

    # # rosette synthesizer  + CVC verfication
    print("====== synthesis")

    candidates = synthesize(
      basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, self.cvcPath, noVerify=(self.cvcPath is None)
    )

    if len(candidates) != 1:
      raise Exception(f"got {len(candidates)} synthesized candidates!")

    # synthesized function should be a fnDecl with body of the form retVal = Expr
    # we remove the retVal part to make it resemble an actual function
    r = candidates[0]
    retVal = cast(Eq, r.body()).e1()

    # TODO: remove ValueRef and other bare values from the input so that we don't need to deal with them here
    args = filter(lambda v: v != retVal, [Var(a.name, a.type) if isinstance(a, ValueRef) else a for a in r.arguments()])
    return FnDecl(r.name(), r.returnT(), cast(Eq, r.body()).e2(), *args)
