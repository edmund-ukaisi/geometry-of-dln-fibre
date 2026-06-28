"""
Robustness: over a WIDER grid (widths 1..4, L<=5), confirm for the (1,1) family
(r=Text(L)=1, c=M[L]=1) that the front-bottleneck min(M[0..L-1])=1 ALWAYS, and characterize p*:
 - is p* ever = L-1 (would force V=I_1, right product empty)? For (1,1), m1=M[L-1]; if p*=L-1 then M[L-1]=1=m1,
   but the smeared condition is r<m1, i.e. 1<m1, so m1>=2 => M[L-1]>=2 => p* != L-1. Confirm.
"""
import itertools, sys
sys.path.insert(0, '/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/genm-frontrank-pnp/expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/scripts')
from witness_tide_validated import achiever
def Text(M,tach,k): return M[0] if k==0 else tach[k-1]
def smeared(maxw, maxL):
    out=[]
    for L in range(2,maxL+1):
      for M in itertools.product(range(1,maxw+1),repeat=L+1):
        M=list(M); T0,mv=achiever(M)
        if mv==0: continue
        tach=[M[0]]+list(T0)
        interior=any(Text(M,tach,k)-Text(M,tach,k+1)>=1 and M[k]-Text(M,tach,k+1)>=1 for k in range(1,L))
        if interior: continue
        if T0[L-2]<M[L-1]: out.append((M,T0,mv,L))
    return out
cases=smeared(4,5)
fam11=[(M,T0,mv,L) for (M,T0,mv,L) in cases if T0[L-2]==1 and M[L]==1]
print(f"WIDER GRID (w<=4, L<=5): (1,1) family = {len(fam11)} cases")
viol=0; pstar_is_Lminus1=0; m1_ge_2=0
for (M,T0,mv,L) in fam11:
    path=[M[k] for k in range(0,L)]
    if min(path)!=1: viol+=1; print("BOTTLENECK!=1", M)
    pstar=path.index(1)
    if pstar==L-1: pstar_is_Lminus1+=1; print("p*=L-1!", M)
    if M[L-1]>=2: m1_ge_2+=1
print(f"  front-bottleneck=1 violations: {viol}")
print(f"  p*=L-1 (empty right product) cases: {pstar_is_Lminus1}")
print(f"  m1=M[L-1]>=2 (so p*!=L-1, since col p* width=1<m1): {m1_ge_2}/{len(fam11)}")
