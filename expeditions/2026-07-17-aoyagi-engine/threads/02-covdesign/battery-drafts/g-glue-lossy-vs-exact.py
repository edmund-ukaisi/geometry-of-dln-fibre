#!/usr/bin/env python3
# guards: theorem4-localization, reduction-layer
# config: (2,2,2) rank-1 non-deepest stratum; exact CoV rlct=3/2 vs lossy naked-weight rlct=1/2
# provenance: threads/02-covdesign (covdesign-t02, D1(a); obligation-2 disease one level up)
"""Glue-level lossy-vs-exact witness: the naked-weight disease at the REGION level.

At a non-deepest point of the (2,2,2) core ||C1.C2||^2 where C1 has rank 1, the
EXACT block-elimination CoV (a unit Jacobian, RLCT-preserving) produces the
monomial ideal (local coords a,b = the regular (1,2) front pivot block; d = the
Schur residual C_4; x,y = the residual (1,2) deep row):

    F_exact  ~  a^2 + b^2 + d^2 (x^2 + y^2)          rlct = 3/2 = 1/2 . minAdm(2,2,2)

A LOSSY "reweighted-residual domination" of the SAME region -- peel the front
(a,b) by a NAKED bound rather than exactly: F >= d^2(x^2+y^2), dropping the
regular front's +1 Morse contribution -- leaves the naked-weighted residual

    F_lossy  =  d^2 (x^2 + y^2)                       rlct = 1/2

whose box integral DIVERGES for every c' in [1/2, 3/2) -- exactly the regime the
engine needs (c' up to 1/2.minAdm = 3/2). The lossy step over-singularises the
residual by d^{-1} (naked d^{-c'} where the exact peel gives the reweighted
d^{1-c'}); this is obligation-2's det(QQ^T)^{-a/2} naked weight, one level up at
region glue, made executable.

Both RLCTs are certified EXACTLY by the Newton-polytope LP (rational vertex
enumeration). Exit 0 iff BOTH compute as stated AND lossy < 1/2.minAdm <= exact
(the design invariant: the region reduction MUST be exact, never a lossy
reweighted domination). No rlct=c* is consumed (circularity guard): the values
come from the monomial LP, not the headline.
"""
import sys
from fractions import Fraction as F
from itertools import combinations


# --- inlined exact Newton-LP (see _rlct.py); rlct(<x^{a_k}>) = min sum u : u>=0, <u,a_k> >= 1/2
def _solve(rows, rhs):
    n = len(rows)
    A = [[F(x) for x in r] + [F(b)] for r, b in zip(rows, rhs)]
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None:
            return None
        A[c], A[piv] = A[piv], A[c]
        inv = A[c][c]
        A[c] = [x / inv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [a - f * b for a, b in zip(A[r], A[c])]
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
            obj = sum(sol)
            best = obj if best is None or obj < best else best
    return best


# minAdm(2,2,2) = 3  (RouteMLayerSplit.minAdmRec, integers only)
minAdm_222 = min((2 - t) * (2 - t) + (t * 2 if t >= 1 else 0) for t in range(3))
half_minAdm = F(minAdm_222, 2)

# vars (a, b, d, x, y): a,b regular front; d.x, d.y coupled residual
F_exact = rlct([(1, 0, 0, 0, 0), (0, 1, 0, 0, 0), (0, 0, 1, 1, 0), (0, 0, 1, 0, 1)], 5)
# lossy: drop the regular front a,b -> naked-weighted residual d.x, d.y (vars d,x,y)
F_lossy = rlct([(1, 1, 0), (1, 0, 1)], 3)

exact_ok = (F_exact == F(3, 2)) and (F_exact == half_minAdm)
lossy_ok = (F_lossy == F(1, 2))
gap = (F_lossy < half_minAdm <= F_exact)   # lossy diverges on [1/2, 3/2); exact reaches 3/2
ok = exact_ok and lossy_ok and gap

print(f"minAdm(2,2,2)={minAdm_222}, half={half_minAdm}")
print(f"EXACT CoV reduction rlct   = {F_exact}  (expect 3/2 = half.minAdm): {exact_ok}")
print(f"LOSSY naked-weight rlct    = {F_lossy}  (expect 1/2): {lossy_ok}")
print(f"lossy < half.minAdm <= exact (region reduction MUST be exact): {gap}")
print(f"=> lossy domination DIVERGES on legal cut c' in [{F_lossy}, {F_exact})")
sys.exit(0 if ok else 1)
