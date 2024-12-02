from itertools import combinations
from typing import Any, List

import numpy as np


def estimator(n: int, c: int, k: int, choices: List[Any]) -> float:
    """
    :param n: total number of samples
    :param c: number of correct samples
    :param k: k in pass@$k$
    """
    # First find all correct solutions
    # TODO: implement is_correct
    correct_indices = set(i for i, choice in enumerate(choices) if is_correct(choice))
    c = 0
    for comb in combinations(range(len(choices)), k):
        if len(comb.intersection(correct_indices)) > 0:
            c += 1
    return 1.0 - np.prod(1.0 - k / np.arange(n - c + 1, n + 1))
