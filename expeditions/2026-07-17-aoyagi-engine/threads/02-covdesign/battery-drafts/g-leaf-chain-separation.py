#!/usr/bin/env python3
# guards: coverage-theorem, region-glue
# config: divisibility-chain leaf Sum b_i^2 = b_1^2.unit => separated form exact; non-chain node undershoots
# provenance: threads/02-covdesign (covdesign-t02, addition 1; region_glue leaf-integrand form)
"""region_glue's SEPARATED product integrand is EXACT at a genuine (divisibility-chain) leaf.

region_glue reads a per-leaf integrand prod_k u_k^{(divExp_k - 1) - 2c'}, threshold min_k divExp_k/2.
Question (architect): at corank >= 2 does the leaf-level finiteness genuinely factor per-divisor, or
must region_glue consult `support` (a COUPLED leaf integrand)?

MECHANISM (settled): Aoyagi's b_i satisfy a DIVISIBILITY CHAIN b_1 | b_2 | ... . Then
   Sum_i b_i^2 = b_1^2 (1 + (b_2/b_1)^2 + ...) = b_1^2 . unit
is a SINGLE dominant monomial times a unit, so rlct = min over b_1's divisors of divExp/2 -- the
SEPARATED form is EXACT. The coupling is absorbed into WHICH divisors form b_1 and their divExp
(= Mval of the sharing-aware profile), set by the sharing-aware case steps -- NOT into the leaf
integrand. So region_glue does NOT need a coupled integrand; its precondition is
IsFullMonomialization (the chain is established).

KILL: a node declared a leaf while its b's are INCOMPARABLE (no chain -- a genuine SUM like the
(2,2,1) residual <d1 x, d2 y>, rlct 1 additive) makes the separated min UNDERSHOOT (1/2 < 1). That
is not a real leaf; it needs more blow-up. So IsFullMonomialization is load-bearing.

Exact (Newton-LP): chain leaf => NewtonLP(Sum b_i^2) == min-over-b_1-divisors divExp/2; incomparable
node => NewtonLP (additive) > naive separated min (undershoot). Exit 0 iff both hold on all cases.
"""
import sys
from fractions import Fraction as F
from itertools import combinations


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


def rlct(gens, nvars):   # Newton-LP: min sum u s.t. <u,alpha_k> >= 1/2, u >= 0
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


ok = True
# chain leaves: b_1 is the smallest (divides the rest); separated = min over b_1's divisors of 1/(2*mult)
chain_cases = [
    ("b1=u1, b2=u1u2",           [(1, 0), (1, 1)], 2, 0),
    ("b1=u1, b2=u1u2, b3=u1u2u3", [(1, 0, 0), (1, 1, 0), (1, 1, 1)], 3, 0),
    ("b1=u1^2, b2=u1^2 u2",      [(2, 0), (2, 1)], 2, 0),
]
for name, gens, nv, b1 in chain_cases:
    true_r = rlct(gens, nv)
    sep = min(F(1, 2 * e) for e in gens[b1] if e > 0)
    m = (true_r == sep); ok &= m
    print(f"[chain] {name:28s} NewtonLP={true_r}  separated(min divExp/2)={sep}  EXACT:{m}")

# non-chain nodes (NOT leaves): incomparable b's -> additive > naive separated min
noncatch = [
    ("Morse b1=u1, b2=u2",            [(1, 0), (0, 1)], 2),
    ("<d1 x, d2 y> (2,2,1) residual", [(1, 0, 1, 0), (0, 1, 0, 1)], 4),
]
for name, gens, nv in noncatch:
    true_r = rlct(gens, nv)
    naive = min(F(1, 2 * e) for g in gens for e in g if e > 0)
    u = (naive < true_r); ok &= u
    print(f"[NON ] {name:28s} NewtonLP(additive)={true_r}  naive-sep-min={naive}  UNDERSHOOT:{u}")

print("SETTLED: separated form exact at a chain leaf; undershoots at a non-chain node "
      "(=> IsFullMonomialization is the precondition; region_glue needs no coupled integrand)"
      if ok else "UNEXPECTED")
sys.exit(0 if ok else 1)
