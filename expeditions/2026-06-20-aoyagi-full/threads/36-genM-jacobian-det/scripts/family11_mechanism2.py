"""
SHARPEN: where does the bottleneck-1 come from? M[0]=1 (output dim) or an inner M[k]=1?
And: is the rank-one-columns property a LITERAL outer product through a Fin-1 INNER dimension,
or through M[0]=1 (then P is 1xm1, trivially rank-<=1 because it has ONE ROW)?
Distinguish the two mechanisms precisely.
"""
import sympy as sp, itertools, os, sys
sys.path.insert(0, '/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/genm-frontrank-pnp/expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/scripts')
from witness_tide_validated import achiever
def Text(M,tach,k): return M[0] if k==0 else tach[k-1]
def smeared():
    out=[]
    for L in range(2,5):
      for M in itertools.product(range(1,4),repeat=L+1):
        M=list(M); T0,mv=achiever(M)
        if mv==0: continue
        tach=[M[0]]+list(T0)
        interior=any(Text(M,tach,k)-Text(M,tach,k+1)>=1 and M[k]-Text(M,tach,k+1)>=1 for k in range(1,L))
        if interior: continue
        if T0[L-2]<M[L-1]: out.append((M,T0,mv,L))
    return out
cases = smeared()
fam11 = [(M,T0,mv,L) for (M,T0,mv,L) in cases if T0[L-2]==1 and M[L]==1]

cat = {'m0=1 (one row)':0, 'inner width-1 layer':0, 'both':0, 'neither(?!)':0}
detail=[]
for (M,T0,mv,L) in fam11:
    r=T0[L-2]; m0=M[0]; m1=M[L-1]
    inner_w1 = [k for k in range(1,L) if M[k]==1]   # inner contracted dims that are 1
    has_m0_1 = (m0==1)
    has_inner1 = len(inner_w1)>0
    if has_m0_1 and has_inner1: cat['both']+=1
    elif has_m0_1: cat['m0=1 (one row)']+=1
    elif has_inner1: cat['inner width-1 layer']+=1
    else: cat['neither(?!)']+=1
    detail.append((tuple(M),L,m0,m1,inner_w1,has_m0_1))

print("(1,1) family bottleneck-1 SOURCE breakdown:")
for k,v in cat.items(): print(f"  {k}: {v}")
print()
# show the cases with neither (if any) -- those would BREAK a pure width-1-layer mechanism
neither=[d for d in detail if not d[5] and not d[4]]
print(f"NEITHER cases (no m0=1, no inner-1): {len(neither)}")
for d in neither: print("   ",d)
print()
# Now the KEY structural question: for cases with m0=1 (one row), m1 can be >1.
# Then P is 1 x m1 -- a single ROW. "rank-one columns" is automatic (each column is a scalar = entry,
#   and col0 is the (1,1) entry, mu_j = P[0,j]/P[0,0]). The cancellation is the SCALAR (1,2,1) form.
# For cases with an inner width-1 layer at position k: the chain FACTORS A^0..A^{k-1} (-> col vec, m0 x 1)
#   times A^k..A^{L-2} (-> row vec, 1 x m1): LITERAL outer product u v^T.
m0_1 = [d for d in detail if d[5]]
print(f"m0=1 cases (P is 1 x m1, scalar/single-row): {len(m0_1)}")
for d in m0_1[:5]: print("   ",d)
print()
inner_only = [d for d in detail if not d[5] and d[4]]
print(f"inner-width-1 ONLY cases (genuine outer product, m0>1): {len(inner_only)}")
for d in inner_only: print("   ",d)
