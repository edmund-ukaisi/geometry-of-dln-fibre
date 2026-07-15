# Shared battery helper (underscore-prefixed: not a runnable witness).
# minAdm(M) via the admissible-corner recursion, plus the ground-truth self-test.
from functools import lru_cache


@lru_cache(maxsize=None)
def minAdm(M):
    """min over corner-peel choices of the accumulated block cost.

    minAdm([m, n])   = m * n
    minAdm(M)        = min_{0<=t<=min(M0,M1)} (M0-t)(M1-t) + minAdm([t] + M[2:])
    """
    M = tuple(M)
    if len(M) < 2:
        raise ValueError("minAdm needs a width list of length >= 2")
    if len(M) == 2:
        return M[0] * M[1]
    best = None
    for t in range(0, min(M[0], M[1]) + 1):
        v = (M[0] - t) * (M[1] - t) + minAdm((t,) + M[2:])
        best = v if best is None else min(best, v)
    return best


GROUND_TRUTHS = {
    (1, 3): 3,
    (2, 2, 2): 3,
    (2, 2, 3): 4,
    (3, 3, 3): 7,
    (3, 3, 4): 8,
    (6, 6, 6): 27,
}


def self_test():
    """Assert every ground truth; raise AssertionError on any mismatch."""
    for M, expected in GROUND_TRUTHS.items():
        got = minAdm(M)
        assert got == expected, f"minAdm({M}) = {got}, expected {expected}"
    return True
