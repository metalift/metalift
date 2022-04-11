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
        (
            "stage0",
            {
                "depth": 2,
                "atoms": [
                    # "add_3_state_vars",
                    "add_2_state_vars",
                    # "add_state_var",
                    # "stateless_arith",
                ],
            },
            {
                "uninterpFuncs": [
                    ("uninterpHash3", 2),
                    ("uninterpHash2", 2),
                ],
                "listBound": 2,
            },
        ),
        (
            "stage1p1",
            {
                "depth": 2,
                "atoms": [
                    # "add_3_state_vars",
                    # "add_2_state_vars",
                    # "nested_ifs",
                    "add_state_var",
                    "stateless_arith",
                ],
            },
        ),
        (
            "stage1p2",
            {
                "depth": 2,
                "atoms": [
                    # "add_3_state_vars",
                    # "add_2_state_vars",
                    # "nested_ifs",
                    "if_else_raw",
                    "add_state_var",
                    # "stateless_arith",
                ],
            },
        ),
        (
            "stage2",
            {"depth": 2, "atoms": ["add_2_state_vars", "stateless_arith"]},
        ),
    ]

    domino.multiple_component_driver(components)
