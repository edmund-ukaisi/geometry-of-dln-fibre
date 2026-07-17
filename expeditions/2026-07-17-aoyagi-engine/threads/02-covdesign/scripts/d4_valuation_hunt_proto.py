#!/usr/bin/env python3
"""D4 exhaustiveness-hunt PROTOTYPE (validate the spec; not the full hunt).

The coverage >=-leg needs: NO divisorial valuation of the core ideal I = <(prod C)_ij>
has ratio < 1/2 minAdm. A decorrelated KILL-HUNT probes MONOMIAL valuations:
assign weight w^{(s)}_{ik} >= 0 to entry c^{(s)}_{ik}. Then
    ord_w((prod C)_{ij}) = min_k sum_s (weights along path i->..->j)   [L=2: min_k w1[i,k]+w2[k,j]]
    ord_w(F) via the ideal:  ord_w(I) = min_{ij} ord_w((prod C)_{ij})
    candidate lct ratio  R(w) = (sum of all weights) / ord_w(I).
lct(F)=lct(I) <= min_w R(w) (monomial-valuation UPPER bound; non-monomial valuations
may lower it -- so a monomial w with R(w) < 1/2 minAdm would REFUTE coverage, but
passing is necessary-not-sufficient). We search small-integer w and report min R(w),
confirming NO monomial valuation undershoots 1/2 minAdm on the tested instances.
"""
import sys
from fractions import Fraction as F
from itertools import product
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
from _minadm import minAdm


def ord_and_ratio_L2(M, w1, w2):
    """L=2 core (M0,M1,M2). w1: M0xM1 weights, w2: M1xM2 weights (tuples of tuples)."""
    M0, M1, M2 = M
    ordI = min(min(w1[i][k] + w2[k][j] for k in range(M1)) for i in range(M0) for j in range(M2))
    tot = sum(sum(r) for r in w1) + sum(sum(r) for r in w2)
    if ordI == 0:
        return None  # valuation does not vanish on I (not centered on the singularity)
    return F(tot, ordI)


def hunt_L2(M, wmax=2):
    M0, M1, M2 = M
    half = F(minAdm(M), 2)
    best = None
    best_w = None
    # search weights in {0..wmax}; skip all-zero
    grids1 = list(product(range(wmax + 1), repeat=M0 * M1))
    grids2 = list(product(range(wmax + 1), repeat=M1 * M2))
    for g1 in grids1:
        w1 = tuple(tuple(g1[i * M1:(i + 1) * M1]) for i in range(M0))
        for g2 in grids2:
            w2 = tuple(tuple(g2[k * M2:(k + 1) * M2]) for k in range(M1))
            r = ord_and_ratio_L2(M, w1, w2)
            if r is None:
                continue
            if best is None or r < best:
                best, best_w = r, (w1, w2)
    return best, half, best_w


if __name__ == "__main__":
    for M in [(2, 2, 2), (2, 2, 3)]:
        best, half, bw = hunt_L2(M, wmax=2)
        undershoot = best < half
        print(f"M={M}: 1/2.minAdm={half}, min monomial-valuation ratio R(w)={best} "
              f"(undershoot? {undershoot})")
        print(f"        argmin w = {bw}")
    print("\nNOTE: min R(w) is the monomial-valuation UPPER bound on lct; if it EQUALS")
    print("1/2.minAdm a monomial valuation is extremal; if it is > , the extremal valuation")
    print("is non-monomial (needs a coordinate change) -- still no monomial undershoot => gate PASS.")
