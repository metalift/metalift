import os
from typing import List

from analysis import CodeInfo, analyze
from ir import *
from synthesize_rosette import synthesize

import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

from domino import DominoLang

domino = DominoLang()


def grammar(ci: CodeInfo):
    # print("Looking at", ci)
    # print("read", ci.readVars)
    # print("mod", ci.modifiedVars)
    name = ci.name

    if name.startswith("inv"):
        raise RuntimeError("no invariants for loop-less grammar")
    else:  # ps
        domino.vars = ci.readVars
        # domino.vars = [Choose(*ci.readVars) for _ in range(7)]
        generated = domino.generate(
            depth=2,
            restrict_to_atoms=[
                # "get_empty_list",
                "add_3_state_vars",
                "if_else_raw",
                "stateless_arith",
            ],
        )
        options = Choose(*list(generated.values()))
        print(generated)

        rv = ci.modifiedVars[0]
        summary = Choose(
            # Eq(rv, options),
            Call("list_eq", Bool(), rv, options),
            # (Call("list_eq", Bool(), rv, Call("Select", List(Int()), *ci.readVars))),
            # (Call("list_eq", Bool(), rv, Call("Select1", List(Int()), *ci.readVars))),
            # (Call("list_eq", Bool(), rv, Call("Select2", List(Int()), *ci.readVars))),
        )
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


if __name__ == "__main__":
    filename = sys.argv[1]
    basename = os.path.splitext(os.path.basename(filename))[0]

    fnName = sys.argv[2]
    loopsFile = sys.argv[3]
    cvcPath = sys.argv[4]

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== lang")
    lang = domino.targetLang()

    print("====== grammar")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    # rosette synthesizer  + CVC verfication
    print("====== synthesis")
    candidates = synthesize(
        basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath
    )
    print("====== verified candidates")
    print("\n\n".join(str(c) for c in candidates))
