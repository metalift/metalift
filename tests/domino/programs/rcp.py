import os

from analysis import CodeInfo
from ir import *

import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

from domino import DominoLang

domino = DominoLang()


def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise RuntimeError("no invariants for loop-less grammar")
    else:  # ps
        domino.set_constants([1, 10, 20])
        domino.set_vars(ci.readVars)
        generated = domino.generate(
            depth=2,
            restrict_to_atoms=[
                # "get_empty_list",
                "mul_acc",
                # "nested_ifs",
                "pred_raw",
                # "add_2_state_vars",
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
        )
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


if __name__ == "__main__":
    domino.driver_function(grammar)
