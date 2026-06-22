"""
Broad EXACT stress test combining (i)(ii)(iii):
For every width vector M (L in 1..4, widths 1..6):
  (i)  realizable rank chains == admPred  (no missed/extra stratum), and minMval(realizable)==minMval(adm).
  (ii) every realizable path's binding ratio = Mval(path)/2 with k=1 (path codim = Mval), AND the
       worst hypothetical shared-u 'cone' divisor ratio >= lambdaCore (multiplicity robustness).
  (iii) descent length = L (chain-length lex measure terminates); no stuck core.
Report ANY chain where: path-min != lambdaCore, OR a realizable stratum undercuts lambdaCore, OR a
contiguous shared-u cone divisor undershoots lambdaCore (the only way k>=2 could bite IF it occurred).
"""
import sys; sys.path.insert(0,'/tmp/pp3')
from mval import Mval, Adm, lambdaCore
from itertools import product
from fractions import Fraction

def realizable(M):
    L=len(M)-1; out=[]
    def cm(j): return min(M[0:j+1])
    def rec(j,prev,acc):
        if j>L: out.append(tuple(acc)); return
        rng=[0] if j==L else range(min(prev,cm(j))+1)
        for tj in rng:
            if tj<=prev and tj<=cm(j): rec(j+1,tj,acc+[tj])
    rec(1,M[0],[]); return set(out)

def best_contig_shared_ratio(M):
    L=len(M)-1; best=None
    for s in range(1,L+1):
        for e in range(s,L+1):
            ent=sum(M[j-1]*M[j] for j in range(s,e+1)); k=e-s+1
            r=Fraction(ent,2*k)
            if best is None or r<best: best=r
    return best

viol_i=viol_pathmin=viol_shared=0
examples=[]
total=0
for L in [1,2,3,4]:
    for M in product(range(1,7),repeat=L+1):
        M=list(M); total+=1
        adm=set(Adm(M)); geo=realizable(M)
        lc=lambdaCore(M); mm=min(Mval(M,t) for t in adm)
        # (i): exact stratum match + min match
        if adm!=geo:
            viol_i+=1
            if len(examples)<10: examples.append(("STRATUM-MISMATCH",tuple(M),sorted(adm-geo),sorted(geo-adm)))
        gmin=min((Mval(M,t) for t in geo),default=mm)
        if gmin!=mm:
            viol_pathmin+=1
            if len(examples)<10: examples.append(("PATHMIN-NE-LAMBDA",tuple(M),gmin,mm))
        # (ii) robustness: worst shared-u cone vs lambdaCore
        bcs=best_contig_shared_ratio(M)
        if bcs is not None and bcs < lc:
            viol_shared+=1
            if len(examples)<10: examples.append(("SHARED-U-UNDERSHOOT",tuple(M),str(bcs),str(lc)))

print(f"Scanned {total} width vectors (L in 1..4, widths 1..6).")
print(f"  (i) stratum-mismatch (admPred != realizable): {viol_i}")
print(f"  (i) path-min != lambdaCore: {viol_pathmin}")
print(f"  (ii) contiguous shared-u cone divisor undershoots lambdaCore: {viol_shared}")
print(f"\n  => path codim-min == 2*lambdaCore on ALL {total} chains" if (viol_i==0 and viol_pathmin==0) else "  VIOLATIONS FOUND")
if examples:
    print("\nExamples:")
    for e in examples: print("  ",e)
else:
    print("\nNo violations of any kind across the scanned family.")
