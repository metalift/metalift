import os

from ir import *

import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

from domino import DominoLang

domino = DominoLang(constants=[0, 1])

if __name__ == "__main__":
    components = [
        (
            "stage0",
            {
                "depth": 2,
                "atoms": [
                    # "add_3_state_vars",
                    # "add_2_state_vars",
                    "if_else_raw",
                    "add_2_state_vars",
                    # "stateless_arith",
                ],
            },
            {
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
                    "nested_ifs",
                    "add_state_var",
                    # "stateless_arith",
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
    ]

    domino.multiple_component_driver(components)
