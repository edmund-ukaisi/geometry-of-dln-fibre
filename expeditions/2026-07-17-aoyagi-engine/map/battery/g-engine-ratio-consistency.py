#!/usr/bin/env python3
# guards: region-glue, exponent-ledger-bridge
# config: the Lean skeleton's ratio form (region_glue hrat + exponent_ledger_bridge) == exact rlct
# provenance: threads/01-skeleton (architect r2, review round-1 item M4); pins the ratio FORM chosen in
#   Engine/EngineObligations.lean against NewtonLP + the minAdm recursion on cert-d3's instances.
"""region_glue's ratio hypothesis is `∀ e ∈ terminalExponents, c' < e/2`, and exponent_ledger_bridge
pins `min terminalExponents = minAdm M`. So the Lean-form finiteness threshold is `½·minAdm M`. This
witness checks that FORM is the exact rlct on the cert's instances, two ways:

(A) BRIDGE numeric — `min terminalExponents = minAdm(M)` and `½·minAdm` equals the paper's rlct on
    the worked chains. The Lean bridge reads `minAdm` (RouteMLayerSplit.minAdmRec, reproduced here
    verbatim); this checks that recursion against Aoyagi's known values (the g-minadm-groundtruth set),
    so ½·(min terminalExponents) is the correct rlct.

(B) SEPARATED per-leaf read — at a genuine divisibility-CHAIN leaf, region_glue's separated
    per-divisor ratio `min_k divExp_k/2` equals NewtonLP(Σ b_i²) EXACTLY (cert-d3 A1); at a
    NON-chain node it UNDERSHOOTS (so IsFullMonomialization / LeafData.bChain is the precondition,
    exactly the C1 fix). This is why region_glue reads the separated form and needs no `support`.

Exit 0 iff (A) holds on all worked chains AND (B) holds (exact at chain leaves, undershoot at
non-chain nodes). Integers/rationals only.
"""
import sys
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product


# ---- (A) the minAdm recursion (verbatim from lean RouteMLayerSplit.minAdmRec) ----
@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(int(x) for x in M)
    if len(M) == 1:
        return 0
    if len(M) == 2:
        return M[0] * M[1]
    return min((M[0] - t) * (M[1] - t) + minAdm((t,) + M[2:])
               for t in range(min(M[0], M[1]) + 1))


# Aoyagi's known values (the g-minadm-groundtruth set): minAdm = 2·rlct_core.
PAPER = {(2, 2, 2): 3, (2, 1, 2): 2, (2, 2, 2, 2): 3, (2, 2, 3): 4, (3, 3, 4): 8}

okA = True
for M, want in PAPER.items():
    got = minAdm(M)                    # the Lean bridge's minAdm = min terminalExponents
    m = (got == want); okA &= m
    print(f"[A bridge] M={M!s:12s} minAdm(recursion)={got}  paper={want}  "
          f"half-threshold={F(got, 2)}  EXACT:{m}")


# ---- (B) NewtonLP + the separated chain-leaf read ----
def _solve(rows, rhs):
    n = len(rows)
    A = [[F(x) for x in r] + [F(b)] for r, b in zip(rows, rhs)]
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None:
            return None
        A[c], A[piv] = A[piv], A[c]
        inv = A[c][c]; A[c] = [x / inv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]; A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return [A[r][n] for r in range(n)]


def rlct(gens, nvars):
    half = F(1, 2)
    cons = [([F(a) for a in g], half) for g in gens]
    for i in range(nvars):
        e = [F(0)] * nvars; e[i] = F(1); cons.append((e, F(0)))
    best = None
    for combo in combinations(range(len(cons)), nvars):
        sol = _solve([cons[c][0] for c in combo], [cons[c][1] for c in combo])
        if sol is None:
            continue
        if all(sum(cf * s for cf, s in zip(cv, sol)) >= rv for cv, rv in cons):
            o = sum(sol); best = o if best is None or o < best else best
    return best


okB = True
# chain leaves: b_1 | b_2 | ... ; separated read = min over b_1's divisors of divExp/2 = NewtonLP
chain = [
    ("b1=u1, b2=u1u2",            [(1, 0), (1, 1)], 2, 0),
    ("b1=u1, b2=u1u2, b3=u1u2u3", [(1, 0, 0), (1, 1, 0), (1, 1, 1)], 3, 0),
    ("b1=u1^2, b2=u1^2 u2",       [(2, 0), (2, 1)], 2, 0),
]
for name, gens, nv, b1 in chain:
    true_r = rlct(gens, nv)
    sep = min(F(1, 2 * e) for e in gens[b1] if e > 0)
    m = (true_r == sep); okB &= m
    print(f"[B leaf ] {name:28s} NewtonLP={true_r}  separated min divExp/2={sep}  EXACT:{m}")
# non-chain node: separated min UNDERSHOOTS (=> not a leaf; needs bChain / IsFullMonomialization)
for name, gens, nv in [("<d1 x, d2 y>", [(1, 0, 1, 0), (0, 1, 0, 1)], 4)]:
    true_r = rlct(gens, nv)
    naive = min(F(1, 2 * e) for g in gens for e in g if e > 0)
    u = (naive < true_r); okB &= u
    print(f"[B non  ] {name:28s} NewtonLP(additive)={true_r}  naive-sep={naive}  UNDERSHOOT:{u}")

ok = okA and okB
print("SETTLED: Lean ratio form (min terminalExponents/2 = ½·minAdm) exact; separated leaf read "
      "= NewtonLP at chain leaves, undershoots off-chain (IsFullMonomialization precondition)."
      if ok else "UNEXPECTED")
sys.exit(0 if ok else 1)
