"""
SHARPEN attack (i): the design's admBound vs the true rank-monotonicity bound.

admBound (Lean):  j=1 -> min(M[0],M[1]);  j>=2 -> M[j+1]  (= M[j] in 0-indexed = the (j+1)-th width)
   i.e. for j (1-indexed, j=1..L), admBound bounds t_j by:
        j=1: min(M[0],M[1])
        j>=2: M[j+1]    (1-indexed M^{j+1}; in 0-indexed python this is M[j])

True rank-monotonicity bound on t_j = rank(A^(1)..A^(j)):
   t_j <= min(M[0], M[1], ..., M[j])   (cumulative min of all widths touched)
   AND  t_j <= t_{j-1}  (non-increasing).

NOTE the weak-decrease t_1>=...>=t_L ALREADY forces t_j <= t_1 <= min(M[0],M[1]). Combined with the
per-layer admBound M[j+1] (1-indexed) = a bound by the *next* layer width. Question: is admPred's set of
t exactly {weakly-decreasing, t_L=0, t_j <= per-layer-bound}, and does that coincide with the
rank-realizable set under cumulative-min? My recursion_model already showed YES on many chains. Here I
brute-force search a LARGE space of chains for ANY mismatch, and ALSO test the dangerous
weakly-decreasing-but-t_L!=0 strata (could the tree blow these up with smaller codim?).
"""
import sys
sys.path.insert(0, '/tmp/pp3')
from mval import Mval, admBound, adm_pred, Adm
from itertools import product, combinations_with_replacement

def realizable(M):
    """rank chains: t_j <= min(M[0..j]), non-increasing, t_L=0."""
    L=len(M)-1
    out=[]
    def cummin(j): return min(M[0:j+1])
    def rec(j,prev,acc):
        if j>L: out.append(tuple(acc)); return
        hi=min(prev,cummin(j))
        rng=[0] if j==L else range(hi+1)
        for tj in rng:
            if tj<=prev and tj<=cummin(j): rec(j+1,tj,acc+[tj])
    rec(1,M[0],[])
    return set(out)

def weakdec_not_lastzero(M):
    """All weakly-decreasing vectors with t_L != 0, bounded by cumulative min -- the 'forbidden'
    strata. Mval over these: if any has Mval < minMval over admissible, AND the tree could reach it,
    that's an obstruction. (The pp-side claim: tree only blows up t_L=0 strata, since {prod=0} forces
    t_L=0.) We report the min Mval over these forbidden strata for awareness."""
    L=len(M)-1
    out=[]
    def cummin(j): return min(M[0:j+1])
    def rec(j,prev,acc):
        if j>L:
            if acc[-1]!=0: out.append(tuple(acc))
            return
        hi=min(prev,cummin(j))
        for tj in range(hi+1):
            if tj<=prev: rec(j+1,tj,acc+[tj])
    rec(1,M[0],[])
    return set(out)

mismatches=0
# Exhaustive search over all width vectors M with L in {2,3,4}, widths 1..5
print("=== Searching for admPred != realizable mismatches and dangerous forbidden strata ===")
for L in [2,3,4]:
    for M in product(range(1,6), repeat=L+1):
        M=list(M)
        adm=set(Adm(M)); geo=realizable(M)
        if adm!=geo:
            mismatches+=1
            print(f"MISMATCH M={tuple(M)}: only_adm={sorted(adm-geo)} only_geo={sorted(geo-adm)}")
        # dangerous-forbidden check
        minMval=min(Mval(M,t) for t in adm)
        forb=weakdec_not_lastzero(M)
        if forb:
            fmin=min(Mval(M,t) for t in forb)
            if fmin < minMval:
                # this forbidden stratum has SMALLER codim. Is it ever a tree center? It would require
                # the product to NOT be zero there. Flag the count, but geometrically t_L!=0 => prod !=0
                # generically => not in {prod=0}, so not a resolution center.
                pass  # we record the worst case below summarily
print(f"total admPred-vs-realizable mismatches over L in 2..4, widths 1..5: {mismatches}")

# Summarize: how often does a forbidden (t_L!=0) stratum undercut minMval? (awareness only)
print("\n=== Forbidden (t_L != 0) strata that UNDERCUT minMval (NOT tree centers if t_L!=0 => prod!=0) ===")
cnt_undercut=0; examples=[]
for L in [2,3]:
    for M in product(range(1,5), repeat=L+1):
        M=list(M)
        adm=set(Adm(M)); minMval=min(Mval(M,t) for t in adm)
        forb=weakdec_not_lastzero(M)
        if forb:
            fmin=min(Mval(M,t) for t in forb)
            if fmin<minMval:
                cnt_undercut+=1
                if len(examples)<6:
                    tmin=min(forb,key=lambda t:Mval(M,t))
                    examples.append((tuple(M),tmin,fmin,minMval))
print(f"count of M where some t_L!=0 stratum has Mval < minMval: {cnt_undercut}")
for M,t,fmin,minMval in examples:
    print(f"  M={M}: forbidden t={t} Mval={fmin} < minMval={minMval}  [t_L={t[-1]}!=0 => prod!=0 => NOT in zero-locus]")
