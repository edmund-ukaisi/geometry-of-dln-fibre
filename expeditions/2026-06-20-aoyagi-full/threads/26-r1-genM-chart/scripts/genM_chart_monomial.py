#!/usr/bin/env python3
"""
genM_chart_monomial.py — does a SINGLE weighted-radial-pivot chart realise ½·minAdm for general M?

The (3,3,4) chart is L=2, single pivot.  Its mechanism:
  - ONE exceptional divisor u_p (the "radial" pivot of the blow-up at the binding rank t_1),
  - F ∘ phi = u_p^2 · U   (U a u_p-free unit, bounded away from 0 on the box),
  - Jacobian |det Dphi| = |u_p|^h · (spectator factors),  with h = minAdm - 1 = 7  on the (3,3,4) leaf.
  - box-divergence threshold = (h+1)/(2k) with (k,h)=(1, minAdm-1) = minAdm/2.   <- the achiever.

THE QUESTION for general M:  the descent has L-1 NESTED pivots t_1,...,t_{L-1}, each a Schur
blow-up.  Does the COMPOSITE chart still factor as  F ∘ Phi = (single monomial)^2 · U  with a
SINGLE binding axis carrying exponent minAdm-1 ?   Or does the nested peel produce a PRODUCT of
exceptional divisors, so the achiever monomial is multi-axis  F = (prod u_{p_i}^{2 a_i}) · U  ?

This script computes, for the descent trace, the candidate single-pivot exponent and tests the
single-axis prediction against minAdm.  Exact integer / rational arithmetic only.

Key arithmetic facts (the threshold of a monomial leaf):
  monomial leaf  integrand  = (prod_j |u_j|^{h_j}) * (|prod_j u_j^{k_j}|^2)^{-c}   [loss base squared]
  the box integral  int_{[0,eps]^N}  diverges at  c >= min_j (h_j + 1)/(2 k_j)  over axes with k_j>0
  (Newton/monomial threshold;  per-axis (h_j+1)/(2 k_j),  the MIN over loss-carrying axes).
For the achiever we WANT the leaf threshold to EQUAL minAdm/2 (so c'>=minAdm/2 diverges, c'<minAdm/2 fin).
"""
from genM_structure import minAdmRec, descent_trace, redChain
from fractions import Fraction as F


def single_pivot_334_style(M):
    """
    The (3,3,4)-style SINGLE-axis prediction:  one binding pivot axis with (k,h)=(1, minAdm-1).
    Threshold = (h+1)/(2k) = minAdm/2.   This is what the (3,3,4) chart did (L=2, one pivot).
    Returns (k, h, threshold).
    """
    val, _ = minAdmRec(tuple(M))
    k = 1
    h = val - 1
    thr = F(h + 1, 2 * k)
    return k, h, thr


def report(M):
    M = tuple(M)
    trace, val = descent_trace(M)
    L = len(M) - 1
    npivots = sum(1 for (_, _, _, kind) in trace if kind == 'recurse')
    k, h, thr = single_pivot_334_style(M)
    print(f"M={M}  L={L}  minAdm={val}  #nested-pivots(>=3-width steps)={npivots}")
    print(f"   single-axis (3,3,4)-style: (k,h)=({k},{h})  threshold=(h+1)/2k={thr}  "
          f"== minAdm/2={F(val,2)}?  {thr == F(val,2)}")
    return npivots, val, thr


if __name__ == "__main__":
    print("=== single-axis (3,3,4)-style prediction vs minAdm/2 ===\n")
    multipivot = []
    for M in [(2, 2, 2), (3, 3, 4), (3, 3, 3), (2, 2, 4), (4, 4, 4), (5, 3, 4),
              (4, 4, 2, 2), (3, 3, 3, 3), (2, 3, 4, 2), (4, 4, 4, 4)]:
        npiv, val, thr = report(M)
        if npiv >= 2:
            multipivot.append(M)
        print()
    print("Cases with >=2 nested pivots (L>=3, the deep-sharing regime):", multipivot)
    print("\nNOTE: the single-axis arithmetic (k,h)=(1,minAdm-1) ALWAYS gives threshold minAdm/2")
    print("by construction.  The real question is whether a single radial pivot CHART can carry")
    print("Jacobian exponent h=minAdm-1 on ONE axis while F=u^2*U.  For L>=3 the nested peel makes")
    print("the composite chart's exceptional set a UNION of divisors -- see genM_chart_geometry.py.")
