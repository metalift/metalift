import os

from ir import *

import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

from domino import DominoLang

domino = DominoLang(constants=[0, 1, 2, 3, 5, 10])

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
        (
            "stage0p1",
            {
                "depth": 3,
                "atoms": [
                    "add_state_var",
                    # "sub",
                    # "mul_acc",
                    "stateless_arith",
                ],
            },
        ),
        ("stage1", {"depth": 2, "atoms": ["sub", "stateless_arith", "add_state_var"]}),
        (
            "stage2",
            {"depth": 2, "atoms": ["stateless_arith", "if_else_raw", "add_state_var"]},
        ),
        (
            "stage3",
            {"depth": 2, "atoms": ["stateless_arith", "if_else_raw", "add_state_var"]},
        ),
        (
            "stage4",
            {
                "depth": 2,
                "atoms": ["stateless_arith", "if_else_raw", "add_3_state_vars"],
            },
        ),
    ]
    for component, kwargs in components:
        grammar = domino.loopless_grammar(**kwargs)
        domino.driver_function(grammar, fnName=component, listBound=4)
