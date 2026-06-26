#!/usr/bin/env python3
"""
iterfibre_class.py — characterize EXACTLY when iterfibre(M) = ½·minAdm, incl. peel-from-either-end +
column-peel (transpose) refinements. The route can peel the OUTER factor from the left (rows = M_0) OR
the right (cols = M_L, by transposing the whole product: ‖P‖²=‖Pᵀ‖²). And the terminal can be either end.

REFINEMENT 1 (peel order / either end): peeling A0 (left, rows M_0) gives threshold M_0/2; peeling
A_{L-1} from the RIGHT (its col count M_L, via transpose: ‖A0…A_{L-1}‖²=‖A_{L-1}ᵀ…A_0ᵀ‖², left factor
A_{L-1}ᵀ has M_L rows) gives threshold M_L/2. So a peel can use min(left-rows, right-cols)? No — each
peel removes ONE outer factor; you choose which END to peel. The general bound iterates peeling from
EITHER end, terminal = the last remaining factor's full Morse. We compute the BEST (max) threshold over
all peel-order/end choices.

Actually the fibre lemma peels the LEFT factor X of a product X·Y, threshold = rows(X). By transposing
we can peel the RIGHT factor (threshold = cols). So at each step we peel an outer factor from whichever
end, threshold = that factor's OUTER dimension (rows if left, cols if right). The terminal single factor
A [a×b] has Morse threshold a·b/2. We maximize the min-threshold over peel sequences.

REFINEMENT 2: can a peel see MORE than its outer dimension? The fibre lemma's threshold is rows(X)/2
regardless of Y — that's the ceiling of the single-column-shear method. We test if peel-order alone
recovers ½·minAdm.
"""
import sys
sys.path.insert(0,'/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/26-r1-genM-chart/scripts')
from genM_structure import minAdmRec
from fractions import Fraction as F
from functools import lru_cache

@lru_cache(maxsize=None)
def best_iterfibre(widths):
    """widths = tuple of boundary widths (M_0,...,M_L); factors are consecutive pairs.
    Peel an outer factor from either end (threshold = its outer dim), recurse; or terminate at 1 factor
    (Morse threshold = product of its two dims /2). Return the BEST (max) guaranteed min-threshold."""
    L = len(widths)-1
    if L == 1:
        # single factor [w0 × w1]: terminal Morse
        return F(widths[0]*widths[1], 2)
    best = F(0)
    # peel LEFT factor A0 [M0×M1]: threshold M0/2, recurse on (M1,...,M_L)
    left = min(F(widths[0],2), best_iterfibre(widths[1:]))
    best = max(best, left)
    # peel RIGHT factor A_{L-1} [M_{L-1}×M_L]: threshold M_L/2, recurse on (M0,...,M_{L-1})
    right = min(F(widths[-1],2), best_iterfibre(widths[:-1]))
    best = max(best, right)
    return best

def report(M):
    M=tuple(M)
    it = best_iterfibre(M)
    ma = F(minAdmRec(M)[0],2)
    st = "MATCH" if it==ma else ("WEAKER" if it<ma else "?!")
    print(f"M={M}: best-iterfibre(either-end)={it}  ½·minAdm={ma}  -> {st}")
    return it==ma

if __name__=="__main__":
    print("Best iterated-fibre (peel either end) vs ½·minAdm:\n")
    results={}
    for M in [(2,2,2),(2,1,2),(4,4,2,2),(2,2,4),(3,3,3),(3,3,4),(3,3,3,3),(4,4,4),(5,3,4),(2,3,4,2),(4,4,4,4),(2,2,2,2),(3,2,3)]:
        results[M]=report(M)
    print("\nMATCH (iterfibre suffices):", [M for M,r in results.items() if r])
    print("WEAKER (needs rank-stratified):", [M for M,r in results.items() if not r])
