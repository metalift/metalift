import os

from ir import *

import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

from domino import DominoLang

domino = DominoLang()

if __name__ == "__main__":
    components = [
        (
            "stage0",
            {
                "depth": 2,
                "atoms": [
                    # "add_3_state_vars",
                    # "add_2_state_vars",
                    "add_state_var",
                    # "stateless_arith",
                ],
            },
            {
                "uninterpFuncs": [
                    ("uninterpHash2", 2),
                ],
                "listBound": 2,
            },
        ),
        (
            "stage1",
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
            "stage2",
            {
                "depth": 2,
                "atoms": [
                    # "add_3_state_vars",
                    # "add_2_state_vars",
                    # "nested_ifs",
                    "if_else_raw",
                    "add_2_state_vars",
                    # "stateless_arith",
                ],
            },
        ),
    ]

    domino.multiple_component_driver(components)
