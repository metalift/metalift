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
                    "add_3_state_vars",
                    # "add_2_state_vars",
                    # "add_state_var",
                    # "stateless_arith",
                ],
            },
            {
                "uninterpFuncs": [
                    ("uninterpHash2a", 2),
                    ("uninterpHash2b", 2),
                    ("uninterpHash2c", 2),
                ],
                "listBound": 3,
            },
        ),
        (
            "stage1",
            {
                "depth": 2,
                "atoms": [
                    "add_3_state_vars",
                    # "add_2_state_vars",
                    # "add_state_var",
                    # "stateless_arith",
                ],
            },
            {
                "uninterpFuncs": [
                    ("uninterpReadSketch1At", 1),
                    ("uninterpReadSketch2At", 1),
                    ("uninterpReadSketch3At", 1),
                ],
                "listBound": 3,
            },
        ),
        (
            "stage2p1p1",
            {"depth": 2, "atoms": ["nested_ifs", "add_state_var"]},
        ),
        (
            "stage2p1p2",
            {"depth": 2, "atoms": ["nested_ifs", "add_state_var"]},
        ),
        (
            "stage2p2p1",
            {"depth": 2, "atoms": ["nested_ifs", "add_state_var"]},
        ),
        (
            "stage2p2p2",
            {"depth": 2, "atoms": ["nested_ifs", "add_state_var"]},
        ),
        (
            "stage2p3",
            {"depth": 3, "atoms": ["if_else_raw", "add_state_var"]},
        ),
        (
            "stage3",
            {"depth": 2, "atoms": ["add_3_state_vars", "stateless_arith"]},
        ),
    ]

    domino.multiple_component_driver(components)
