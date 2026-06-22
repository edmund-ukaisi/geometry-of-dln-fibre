"""
Independent model of the iterated-pivot resolution recursion, to test whether
the set of root-to-leaf PATHS reproduces the admissible-stratum codim-min (Mval).

I do NOT assume the design's claim. I model the recursion from the geometry of the
matrix chain F = ||A^(1) ... A^(L)||^2 and check the path<->stratum correspondence
EXACTLY against the Mval ground truth (mval.py).

==== The recursion mechanism (my independent reconstruction) ====
At the deepest singular point A=0, the whole chain product is 0. Resolving {prod=0}:
the standard flag/Schur resolution proceeds layer by layer. Think of it as: we record,
for each layer s, how much rank the partial product KEEPS (call it the "rank kept" r_s),
equivalently how much the kernel grows. The admissible exponent t_j in Mval is exactly
the rank data t_j = rank kept at step j (with t_L = 0 because the full product is rank 0
on {prod=0}), weakly decreasing because ranks can only drop along the chain, bounded by
the layer widths.

The blow-up at layer j with a chosen rank-kept value t_j contributes a coordinate-subspace
center of codimension = number of residual entries forced to vanish at that layer:
  block j=1:   (M[0]-t_1)(M[1]-t_1)
  block j>=2:  (t_{j-1}-t_j)(M[j+1]-t_j)
summing to Mval(M,t). So a PATH that realizes rank-kept vector t accumulates total
exceptional codim = Mval(M,t), binding ratio (h+1)/(2k) = Mval/2 (h = Mval-1, k=1).

==== The test ====
The atlas reaches stratum t iff the rank-kept vector t is REALIZABLE as a weakly-decreasing
chain with t_L=0 and per-block bounds. That is EXACTLY admPred. So {paths} <-> {admissible t}
SHOULD be the identity correspondence. I test this by:
  (A) enumerating all admissible t (= reachable paths, by the above identification),
  (B) confirming each path's accumulated codim = Mval(M,t),
  (C) confirming min over paths = minMval = 2*lambdaCore.
The OBSTRUCTION would be: an admissible t with Mval(M,t) < minMval that is somehow NOT a path,
OR a path reaching a stratum of codim < minMval. Since paths <-> admissible t is the identity
(by construction of admPred = realizable rank-kept chains), surjectivity is automatic IF the
identification is correct. The real risk is whether admPred captures EXACTLY the realizable
chains -- neither too many (a t with no geometric path) nor too few (a realizable chain not in
admPred). I stress this below with the rank-monotonicity constraints.
"""
import sys
sys.path.insert(0, '/tmp/pp3')
from mval import Mval, admBound, adm_pred, Adm, lambdaCore, adm_with_vals
from fractions import Fraction

def realizable_rank_chains(M):
    """
    Independent enumeration of geometrically-realizable 'rank-kept' chains for the chain product
    A^(1)...A^(L), A^(s): M[s-1] x M[s]. A rank-kept vector t=(t_1..t_L):
      t_j = rank of the partial product A^(1)...A^(j)  (an M[0] x M[j] matrix).
    Constraints from linear algebra (EXACT, not the design's admPred):
      - t_j <= min over the chain so far of the layer widths touched:
            rank(A^(1)..A^(j)) <= min(M[0], M[1], ..., M[j]).
      - rank is NON-INCREASING along the chain: t_1 >= t_2 >= ... (rank(XY) <= rank(X)).
        Actually rank(A^(1)..A^(j)) <= rank(A^(1)..A^(j-1)) AND <= rank(A^(j)). So t_j <= t_{j-1}.
      - on the zero-locus {prod=0}: t_L = rank(full product) = 0.
      - t_1 = rank(A^(1)) <= min(M[0],M[1]).
    Enumerate ALL such chains and return as a set of tuples.
    """
    L = len(M) - 1
    chains = []
    # cumulative min of widths up to layer j (1-indexed partial product touches M[0..j])
    def cummin(j):  # j = 1..L, partial product A^(1)..A^(j) is M[0] x M[j]
        return min(M[0:j+1])
    def rec(j, prev, acc):
        if j > L:
            chains.append(tuple(acc))
            return
        # t_j ranges 0..min(prev, cummin(j)); on zero-locus t_L=0
        hi = min(prev, cummin(j))
        if j == L:
            rng = [0]  # forced t_L = 0 on the zero-locus
        else:
            rng = range(0, hi+1)
        for tj in rng:
            if tj <= prev and tj <= cummin(j):
                rec(j+1, tj, acc+[tj])
    rec(1, M[0], [])  # t_0 conceptually = rank of empty product = M[0] (full)
    return set(chains)

def compare(M):
    M = list(M)
    adm = set(Adm(M))                       # design's admissible set (admPred)
    geo = realizable_rank_chains(M)         # my independent realizable rank chains
    minMval = min(Mval(M, t) for t in adm)
    print(f"M={tuple(M)}")
    print(f"  |Adm(admPred)|={len(adm)}  |realizable rank chains|={len(geo)}")
    only_adm = adm - geo
    only_geo = geo - adm
    if only_adm:
        print(f"  IN admPred but NOT realizable: {sorted(only_adm)}")
    if only_geo:
        print(f"  REALIZABLE but NOT in admPred (POSSIBLE MISSED/EXTRA STRATUM): {sorted(only_geo)}")
        for t in sorted(only_geo):
            print(f"      t={t}  Mval={Mval(M,t)}  (minMval over admPred = {minMval})")
    if not only_adm and not only_geo:
        print(f"  admPred == realizable rank chains  [EXACT MATCH]")
    # codim-min comparison: over the realizable set
    geo_min = min((Mval(M,t) for t in geo), default=None)
    print(f"  minMval(admPred)={minMval}  minMval(realizable)={geo_min}  lambdaCore={lambdaCore(M)}")
    if geo_min is not None and geo_min < minMval:
        print(f"  *** OBSTRUCTION (i): realizable stratum with codim {geo_min} < admPred min {minMval} ***")
    print()

if __name__ == "__main__":
    for M in [(2,2,2),(2,1,2),(1,2,1),(3,1,3),(2,3,2),(3,2,1),(1,2,3),
              (3,3,3,3),(2,2,2,2),(4,2,4),(2,4,2),(3,2,3),(1,3,1),(4,1,4),
              (2,2,2,2,2),(3,2,2,3),(5,3,5)]:
        compare(M)
