import os

from ir import *

import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

from domino import DominoLang

domino = DominoLang()

"""
"mul_acc",
"nested_ifs",
"sub",
"add_2_state_vars",
"add_3_state_vars",
"if_else_raw",
"stateless_arith",
"""


if __name__ == "__main__":
    components = [
        ("test", {"depth": 2, "atoms": ["if_else_raw", "add_3_state_vars"]}),
    ]
    for component, kwargs in components:
        grammar = domino.loopless_grammar(**kwargs)
        domino.driver_function(grammar, fnName=component, listBound=3)
