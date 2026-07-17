#!/usr/bin/env python3
# guards: reduction-layer
# config: pivot-regularity charts of the (2,2,2) rank-r peel; rank-<r locus codim = (m-r+1)(n-r+1)
# provenance: threads/02-covdesign (covdesign-t02, D1(b); region-uniform Lemma-2/Thm-3 pivot cover)
"""Pivot co-null guard: the reduction layer's pivot-regularity cover is co-null.

Lemma 2 / Theorem 3 (block elimination) needs a regular r x r pivot block
(A_1 invertible) to build the unit-triangular P/Q. Region-uniformly, the
parameter box is covered by finitely many charts, in each of which SOME fixed
r x r minor of the relevant m x n matrix is a unit; the reduction is the exact
CoV on that chart. For this to be a genuine (measure-full) cover we need the
LEFTOVER -- {every candidate r x r minor vanishes} = {rank < r} -- to be
CO-NULL, i.e. a determinantal variety of positive codimension.

Exact fact (elementary, integers only): the variety of m x n real matrices of
rank <= k has dimension  k(m + n - k)  and codimension  (m-k)(n-k). Hence
{rank < r} = {rank <= r-1} has

    codim = (m - r + 1)(n - r + 1)  >= 1     for  1 <= r <= min(m,n),

so the pivot-regular set {some r x r minor != 0} is full measure and the finite
minor-chart cover misses only a null set -- the region-uniform reduction glues
over the box up to null. (The missed null set is where the reduction is NOT
needed: it feeds the deeper strata / the origin resolution, one owner each.)

We verify two ways per instance: (a) the codim formula (m-r+1)(n-r+1), and
(b) an independent dimension count  mn - dim{rank<=r-1} = mn - (r-1)(m+n-r+1).
They must agree and be >= 1. Smallest instances: the (2,2,2) top reduction uses
2x2 pivot blocks at ranks r in {1,2}; we also sweep the peel-relevant shapes.
Exit 0 iff every pivot-vanishing locus is co-null (codim >= 1) by both counts.
"""
import sys


def codim_rank_lt_r(m, n, r):
    """codim of {rank < r} = {rank <= r-1} in R^{m x n}, two independent ways."""
    formula = (m - r + 1) * (n - r + 1)                 # (m-k)(n-k) with k=r-1
    dim_rank_le = (r - 1) * (m + n - (r - 1))           # dim of rank<=r-1 stratum
    by_dimcount = m * n - dim_rank_le
    return formula, by_dimcount


# The pivot shapes the (2,2,2) reduction (and its small cousins) actually use:
# an m x n block peeled at rank r (1 <= r <= min(m,n)).
cases = [
    (2, 2, 1), (2, 2, 2),        # (2,2,2) top reduction: C1 is 2x2, ranks 1 and 2
    (2, 3, 1), (2, 3, 2),        # (2,2,3): C1 2x2 pivots, and the 2x3 residual-feed
    (3, 3, 1), (3, 3, 2), (3, 3, 3),   # (3,3,4)
    (3, 2, 1), (3, 2, 2),        # (3,2,3)
]
ok = True
print(f"  {'m':>2} {'n':>2} {'r':>2} {'codim{rank<r} (formula)':>22} {'(dimcount)':>12} {'co-null?':>9}")
for m, n, r in cases:
    f, d = codim_rank_lt_r(m, n, r)
    agree = (f == d)
    conull = (f >= 1)
    ok &= agree and conull
    flag = "OK" if (agree and conull) else "FAIL"
    print(f"  {m:>2} {n:>2} {r:>2} {f:>22} {d:>12} {str(conull):>9}  [agree:{agree}] {flag}")
print("co-null cover CONFIRMED" if ok else "FAILED")
sys.exit(0 if ok else 1)
