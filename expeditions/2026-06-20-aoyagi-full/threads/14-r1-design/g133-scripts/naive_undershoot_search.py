"""
Exhaustive search: does the naive all-origin divisor (ratio N/(2L), k_E=L) EVER undershoot lambdaCore?
Undershoot <=> N/(2L) < lambdaCore = minMval/2  <=>  N < L * minMval.
Also report the k=L divisor ratio vs the binding to understand the safety margin.
This is the WORST shared-u divisor; if even IT never undershoots, the multiplicity trap is contained
for the all-origin divisor (still must check the FAITHFUL atlas divisors, done separately).
"""
import sys; sys.path.insert(0,'/tmp/pp3')
from mval import Mval, Adm, lambdaCore
from itertools import product
from fractions import Fraction

def N_entries(M):
    L=len(M)-1
    return sum(M[s-1]*M[s] for s in range(1,L+1))

def minMval(M):
    return min(Mval(M,t) for t in Adm(M))

worst=[]
count_under=0
for L in [1,2,3,4]:
    for M in product(range(1,7), repeat=L+1):
        M=list(M)
        N=N_entries(M); mm=minMval(M)
        # undershoot of naive divisor: N < L*mm
        lhs=Fraction(N,2*L); rhs=Fraction(mm,2)
        margin = lhs - rhs
        if N < L*mm:
            count_under+=1
            worst.append((tuple(M),N,L,mm,lhs,rhs))
print(f"naive all-origin divisor undershoots (N < L*minMval) in {count_under} cases over L<=4 widths 1..6")
for w in worst[:20]:
    print("  ", w)

# Also: the SHARED-u over a SUBSET of k factors. Most dangerous = scaling k adjacent factors with one u.
# That divisor (if it existed in the atlas): scale factors s..s+k-1 by u. Then prod scales by u^k on the
# affected portion; ord_u(F) along it depends on which entries. The faithful atlas does NOT build these,
# but quantify the worst subset-ratio to bound the trap. (Heuristic upper bound on danger.)
print("\nMinimum over k of (entries scaled)/(2k) for contiguous-factor shared-u, vs lambdaCore:")
def best_shared_ratio(M):
    L=len(M)-1
    # scaling factors [s..e] (1-indexed) by u: entries scaled = sum_{j=s..e} M[j-1]*M[j]; k=e-s+1
    # Jacobian h = (entries scaled)-1 IF the chart is the cone blow-up on those entries; ratio=(entries)/(2k)
    best=None
    for s in range(1,L+1):
        for e in range(s,L+1):
            ent=sum(M[j-1]*M[j] for j in range(s,e+1))
            k=e-s+1
            r=Fraction(ent,2*k)
            if best is None or r<best: best=r
    return best
for M in [(2,2,2),(3,1,3),(2,2,2,2),(2,2,2,2,2),(5,1,5),(2,1,2),(10,1,10),(1,1,1)]:
    M=list(M)
    print(f"  M={tuple(M)}: best contiguous shared-u ratio={best_shared_ratio(M)}  lambdaCore={lambdaCore(M)}")
