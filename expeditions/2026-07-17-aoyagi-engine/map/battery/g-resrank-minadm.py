#!/usr/bin/env python3
# guards: exponent-ledger-bridge (resRank fold), region-glue (residual ratio)
# config: the terminalExponents resRank fold's truth-witness `resRank_l >= minAdm M`
# provenance: threads/rung2 (architect-t02, 2026-07-18); the resRank-vs-minAdm satisfiability check
#   the divisor-ratio hunt did NOT cover (priorities #3; bridge-cert §4 verified only 3 charts, and with
#   the WRONG rank convention — see FINDING below).
"""
`terminalExponents` folds each leaf's Morse-residual rank `resRank` into the exponent list, and
`exponent_ledger_bridge` requires `minAdm M <= e` for EVERY terminal exponent `e` — INCLUDING the
folded `resRank`. So the residual must never bind below `1/2 minAdm`: the truth-witness is

    resRank_l  >=  minAdm M     for every leaf l with positive resRank.

This script is the smallest-instance satisfiability check on (2,2,2), (2,2,4), (3,3,4), (2,2,2,2).

THE THRESHOLD-CORRECT RANK CONVENTION (the FINDING this script pins).
The residual `R` of a chart is `F o phi / (divisor monomial)`, restricted to the exceptional fibre
(divisors = 0); it is a sum of squares `||G(z)||^2` of the residual-normalised generators. The
radial read `INT ||G||^{-2c'}` near the core `{G=0}` converges iff `c' < rho/2`, where `rho` is the
TRANSVERSE (on-core) Morse rank = rank of the Hessian of `R` at a GENERIC point of `{G=0}` (= codim
of the core). This is NOT the GENERIC-ambient Hessian rank (`sympy .rank()` of the symbolic Hessian),
which over-counts off the core: e.g. (2,2,2) delta-chart gives generic 5 but transverse 4; the
(2,2,4) core gives generic 11 but transverse 8. bridge-cert §4's tabulated "Morse rank 5 / 8" mixed
the two conventions. The truth-witness must use the SMALLER (transverse) rank — that is the binding
threshold — so this script computes and checks THAT.

mono is divisor-only, so Hess_z(F/mono) = Hess_z(F)/mono and rank is unaffected: we compute the
Hessian of `F = sum(entry^2)` over the non-divisor coords, at (divisors generic-nonzero, residual
coords on the core), and take its rank. Exact rational arithmetic (a certified rank for that point;
= the generic-on-core rank with probability 1 over the random gauge/divisor values).

SCOPE CAVEAT (honest). At corank >= 2 the residual of an INTERMEDIATE chart is itself a coupled,
recursive DLN core (the (3,3,4) corank-2 chart's residual IS the (2,2,4) core) — NOT a clean Morse
core; only a TRUE (fully monomialised) leaf has `R = ||z||^2` clean. Constructing the genuine
deepest L=3 leaf of (2,2,2,2) is the separate L=3 de-risk; here (2,2,2,2) is checked on its
t=2-reduction leaf (a legitimate leaf whose residual = the (2,2,2) core). The corank-2 (2,2,4) /
(3,3,4) cores are checked as the deepest constructible residual (an intermediate node) — a NECESSARY
check (if the residual rank there undershot minAdm the fold would already be unsound).

Exit 0 iff resRank_transverse >= minAdm on every tested chart. Integers/rationals only.
"""
import sys
import random
from functools import lru_cache
import sympy as sp

random.seed(20260718)


# ---- minAdm recursion (verbatim from lean RouteMLayerSplit.minAdmRec) ----
@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(int(x) for x in M)
    if len(M) == 1:
        return 0
    if len(M) == 2:
        return M[0] * M[1]
    return min((M[0] - t) * (M[1] - t) + minAdm((t,) + M[2:])
               for t in range(min(M[0], M[1]) + 1))


def ranks(prod_entries, coords, div_names, core_vanish):
    """Return (F_vanishes_on_core, transverse_rank, generic_rank).
    transverse_rank = rank Hess_z(F) at (divisors generic, core_vanish coords = 0, gauge random) —
    the threshold-relevant residual rank. generic_rank = rank at a fully-random point (the
    bridge-cert convention), reported for contrast."""
    div = [c for c in coords if c.name in div_names]
    z = [c for c in coords if c.name not in div_names]
    F = sp.expand(sum(e ** 2 for e in prod_entries))
    # transverse (on-core) evaluation point
    sub_t = {d: sp.Integer(random.randint(2, 7)) for d in div}
    for c in z:
        sub_t[c] = sp.Integer(0) if c.name in core_vanish else sp.Integer(random.randint(-7, 7))
    Fcore = F.subs(sub_t)
    Ht = sp.Matrix(len(z), len(z), lambda i, j: sp.diff(F, z[i], z[j]).subs(sub_t))
    # generic (ambient) evaluation point
    sub_g = {c: sp.Integer(random.randint(2, 7)) for c in div}
    sub_g.update({c: sp.Integer(random.randint(-7, 7)) for c in z})
    Hg = sp.Matrix(len(z), len(z), lambda i, j: sp.diff(F, z[i], z[j]).subs(sub_g))
    return (Fcore == 0, Ht.rank(), Hg.rank())


al, a, b, de, up, vp, r, s = sp.symbols("alpha a b delta up vp r s", real=True)


def chart_222_delta():
    A = sp.Matrix([[al, al * a], [al * b, al * (a * b + de)]])
    B = sp.Matrix([[de * up - a * r, de * vp - a * s], [r, s]])
    AB = sp.expand(A * B)
    return ([AB[i, j] for i in range(2) for j in range(2)],
            [al, a, b, de, up, vp, r, s], {"alpha", "delta"}, {"up", "vp", "r", "s"})


def chart_full_block_2x4():
    """Full-block (Case-2, corank-2) blow-up A = de2*E (E = [[1,e1],[e2,e3]]) times a free 2x4 S.
    This IS both the (2,2,4) deepest full-block chart AND the (3,3,4) corank-2 chart's residual
    sub-core (block-elim identification, D2 census)."""
    de2, e1, e2, e3 = sp.symbols("de2 e1 e2 e3", real=True)
    S = sp.Matrix(2, 4, lambda i, j: sp.Symbol(f"s_{i}{j}", real=True))
    A = sp.Matrix([[de2, de2 * e1], [de2 * e2, de2 * e3]])
    prod = sp.expand(A * S)
    coords = [de2, e1, e2, e3] + [S[i, j] for i in range(2) for j in range(4)]
    core = {f"s_{i}{j}" for i in range(2) for j in range(4)}
    return ([prod[i, j] for i in range(2) for j in range(4)], coords, {"de2"}, core)


CASES = [
    ("(2,2,2) delta-chart [true leaf]", (2, 2, 2), chart_222_delta()),
    ("(2,2,4) full-block [deepest full-block chart]", (2, 2, 4), chart_full_block_2x4()),
    ("(3,3,4) corank-2 [intermediate; residual = (2,2,4) core]", (3, 3, 4), chart_full_block_2x4()),
    ("(2,2,2,2) t=2-reduction leaf [= (2,2,2) core]", (2, 2, 2, 2), chart_222_delta()),
]

ok = True
print(f"{'chart':52s} {'minAdm':>7s} {'rho_transverse':>15s} {'(generic)':>10s} {'>=minAdm?':>10s}")
for name, M, (ents, coords, divs, core) in CASES:
    m = minAdm(M)
    vanishes, rho_t, rho_g = ranks(ents, coords, divs, core)
    good = vanishes and rho_t >= m
    ok &= good
    print(f"{name:52s} {m:7d} {rho_t:15d} {rho_g:10d} {'OK' if good else 'FAIL':>10s}"
          + ("" if vanishes else "  [core does NOT vanish!]"))

print()
print("minAdm(2,2,2,2) =", minAdm((2, 2, 2, 2)),
      "(genuine non-reducing L=3 leaf: separate L=3 de-risk; not constructed here)")
print("RESULT:", "PASS — resRank_transverse >= minAdm on every tested chart" if ok
      else "FAIL — a residual rank undershoots minAdm (KILL-CONDITION)")
sys.exit(0 if ok else 1)
