from typing import Any, Callable, Dict, List, Optional, Union, cast

from llvmlite.binding import ValueRef

from metalift.analysis import analyze
from metalift.ir import Eq, Expr, FnDeclRecursive, NonTerm, Synth, Target, Var
from metalift.synthesize_auto import synthesize  # type: ignore


class Transpiler:
    grammar: Optional[
        Callable[[List[Union[Any, Expr]], Union[Any, Expr], bool], Dict[NonTerm, Expr]]
    ]
    cvcPath: str

    def __init__(
        self,
        grammar: Callable[
            [List[Union[Any, Expr]], Union[Any, Expr], bool], Dict[NonTerm, Expr]
        ],
        cvcPath: str = "",
    ) -> None:
        self.grammar = grammar
        self.cvcPath = cvcPath

    def expand(
        self,
        name: str,
        readVars: List[Union[Any, Expr]],
        modifiedVars: List[Union[Any, Expr]],
        generatedGrammar: Dict[NonTerm, Expr],
    ) -> Synth:
        return Synth(
            name,
            Eq(modifiedVars[0], list(generatedGrammar.values())[0]),
            *modifiedVars,
            *readVars,
        )

    def transpile(self, filename: str, fnName: str, loopsFile: str = "") -> Expr:
        if loopsFile == "":
            if filename.endswith(".ll"):
                loopsFile = filename[:-2] + "loops"

        print(f"======= input: {filename}, fn: {fnName}, loops: {loopsFile}")
        (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(
            filename, fnName, loopsFile
        )

        print("====== generating grammar")

        basename = fnName

        if self.grammar:
            invAndPs = [
                self.expand(
                    basename,
                    ci.read_vars,
                    ci.modified_vars,
                    self.grammar(
                        ci.read_vars, ci.modified_vars[0], ci.name.startswith("inv")
                    ),
                )
                for ci in loopAndPsInfo
            ]

        lang = list(Target.definedFns.values())

        # # rosette synthesizer  + CVC verfication
        print("====== synthesis")

        candidates = synthesize(
            basename,
            lang,
            vars,
            invAndPs,
            preds,
            vc,
            loopAndPsInfo,
            self.cvcPath,
            no_verify=(self.cvcPath is None),
        )

        if len(candidates) != 1:
            raise Exception(f"got {len(candidates)} synthesized candidates!")

        # synthesized function should be a fnDecl with body of the form retVal = Expr
        # we remove the retVal part to make it resemble an actual function
        r = candidates[0]
        retVal = cast(Eq, r.body()).e1()

        # TODO: remove ValueRef and other bare values from the input so that we don't need to deal with them here
        args = filter(
            lambda v: v != retVal,
            [
                Var(a.name, a.type) if isinstance(a, ValueRef) else a
                for a in r.arguments()
            ],
        )
        return FnDeclRecursive(r.name(), r.returnT(), cast(Eq, r.body()).e2(), *args)
