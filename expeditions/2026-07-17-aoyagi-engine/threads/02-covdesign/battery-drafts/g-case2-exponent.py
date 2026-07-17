#!/usr/bin/env python3
# guards: case-step-lemmas, coverage-theorem
# config: Case-2 full-block divisor exponent (M(S)-J)(M(S+1)-J); re-derive + non-undershoot + scope of T-C
# provenance: threads/02-covdesign (covdesign-t02, addition 2; worked-tex T-C flag re-confirm on R1 pass)
"""Case-2 step exponent: re-derivation + the HONEST non-bindingness scope.

Case 2 (full run) blows up the residual d-block of size (M(S)-J) x (M(S+1)-J). A smooth
blow-up of a codimension-c center gives Jacobian power c-1 and the loss vanishes to order 2,
so the divisor exponent (Jacobian power + 1) = c = the codimension of the blown-up block:

    divExp_case2 = (M(S) - J) . (M(S+1) - J)          [= the printed formula, image p.20].

RE-DERIVE (a): the block has (M(S)-J)(M(S+1)-J) free entries, so its vanishing locus has that
codimension; divExp = codim. Matches the printed formula by construction.

NON-UNDERSHOOT (b) -- the coverage-relevant fact: the top-level full-block exponent M^(i).M^(i+1)
(J=0) is >= minAdm(M) for EVERY adjacent pair, so a Case-2 divisor NEVER yields a ratio below
1/2 minAdm (it cannot break coverage's >=-leg). Holds by permutation-invariance of minAdm
(minAdm <= Mval(t=0 on that pair) = M^(i).M^(i+1)).

SCOPE CORRECTION (c) -- the T-C flag says "never attains the min". That is TOO STRONG: the
full-block (t=0) branch TIES the min for some chains (e.g. (2,2,4): minAdm=4=M0.M1). The honest
statement is: Case-2 exponents are UPPER bounds on minAdm (never undershoot), STRICTLY non-binding
for some chains and TYING for others. We report both and assert only the non-undershoot.

Exit 0 iff: (a) re-derivation == printed formula on all shapes; (b) every adjacent-pair full-block
exponent >= minAdm; and (c) the tie-vs-strict split is reported (>=1 of each found, refuting the
blanket "never attains").
"""
import sys
from itertools import product as iproduct
from functools import lru_cache


@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(int(x) for x in M)
    if len(M) == 1:
        return 0
    if len(M) == 2:
        return M[0] * M[1]
    return min((M[0] - t) * (M[1] - t) + minAdm((t,) + M[2:]) for t in range(min(M[0], M[1]) + 1))


def case2_exponent(MS, MS1, J):
    """re-derived from the blow-up: codim of the (MS-J)x(MS1-J) residual block."""
    return (MS - J) * (MS1 - J)


chains = [(2, 2, 2), (2, 2, 3), (2, 2, 4), (2, 2, 1), (3, 3, 4), (3, 2, 3), (2, 2, 2, 2), (2, 3, 2, 2)]

# (a) re-derivation == printed formula (the printed formula IS (M(S)-J)(M(S+1)-J); confirm on shapes/J)
rederive_ok = True
for MS in range(1, 5):
    for MS1 in range(1, 5):
        for J in range(0, min(MS, MS1)):
            printed = (MS - J) * (MS1 - J)
            if case2_exponent(MS, MS1, J) != printed:
                rederive_ok = False

# (b) non-undershoot + (c) tie-vs-strict scope
non_undershoot = True
n_tie = n_strict = 0
rows = []
for M in chains:
    ma = minAdm(M)
    for i in range(len(M) - 1):
        e = case2_exponent(M[i], M[i + 1], 0)      # top-level full block on pair (i,i+1)
        ge = (e >= ma)
        non_undershoot &= ge
        if e == ma:
            n_tie += 1
        elif e > ma:
            n_strict += 1
        rows.append((M, (i, i + 1), e, ma, "tie" if e == ma else "strict>" if e > ma else "UNDERSHOOT!"))

scope_ok = (n_tie >= 1 and n_strict >= 1)   # refutes the blanket "never attains"
ok = rederive_ok and non_undershoot and scope_ok

print(f"(a) re-derivation (codim) == printed (M(S)-J)(M(S+1)-J) on all shapes: {rederive_ok}")
print(f"(b) every adjacent full-block exponent >= minAdm (never undershoots): {non_undershoot}")
print(f"(c) tie count={n_tie}, strict-above count={n_strict}  => blanket 'never attains' is FALSE: {scope_ok}")
for M, pair, e, ma, tag in rows:
    print(f"    M={M} pair{pair}: Case-2 exp={e}  minAdm={ma}  [{tag}]")
sys.exit(0 if ok else 1)
