import os

from ir import *

import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

from domino import DominoLang

domino = DominoLang(constants=[0, 1, 10, 20, 2000])

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
        (
            "stage0p2",
            {
                "depth": 2,
                "atoms": [
                    "add_state_var",
                    # "sub",
                    # "mul_acc",
                    "stateless_arith",
                ],
            },
        ),
        (
            "stage0p3",
            {
                "depth": 2,
                "atoms": [
                    "if_else_raw",
                    "add_state_var",
                    # "sub",
                    # "mul_acc",
                ],
            },
        ),
        (
            "stage1p1",
            {
                "depth": 2,
                "atoms": ["stateless_arith", "add_state_var"],
            },
        ),
        (
            "stage1p2",
            {
                "depth": 2,
                "atoms": ["if_else_raw", "add_2_state_vars"],
            },
        ),
        (
            "stage2p1",
            {"depth": 3, "atoms": ["stateless_arith", "add_state_var"]},
        ),
        (
            "stage2p2",
            {"depth": 2, "atoms": ["stateless_arith", "add_state_var"]},
        ),
        (
            "stage2p3",
            {"depth": 2, "atoms": ["if_else_raw", "add_state_var"]},
        ),
        (
            "stage3p1",
            {"depth": 3, "atoms": ["stateless_arith", "add_state_var"]},
        ),
        (
            "stage3p2",
            {"depth": 2, "atoms": ["if_else_raw", "add_state_var"]},
        ),
        (
            "stage4",
            {"depth": 2, "atoms": ["stateless_arith", "add_2_state_vars"]},
        ),
    ]

    domino.multiple_component_driver(components)
