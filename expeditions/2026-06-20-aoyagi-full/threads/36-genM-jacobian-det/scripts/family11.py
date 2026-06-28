import sys; sys.path.insert(0,'.')
import pp_smear_GATE as G
from collections import Counter
cases = G.smeared()
fam11 = [(M,T0,L) for M,T0,mv,L in cases if T0[L-2]==1 and M[L]==1]
print("(1,1) family: count =", len(fam11))
byL = Counter(L for _,_,L in fam11)
print("by L:", dict(sorted(byL.items())))
# what varies: L, the front widths M[0..L-1], the pivot location (the bottleneck k where M[k]=r=1)
# the pivot 'k' (front layer with M_k = r = 1):
import itertools
print("\nsample members (M, L, pivot-layer where M_k=1, s=m1-r):")
for M,T0,L in sorted(fam11, key=lambda x:(x[2], sum(x[0])))[:14]:
    r=T0[L-2]; m1=M[L-1]; s=m1-r
    # bottleneck: smallest k in [0,L-1] with M[k]=r
    pivotk = min(k for k in range(L) if M[k]==r)
    N=sum(M[k]*M[k+1] for k in range(L))
    print(f"  M={M} L={L} pivotk={pivotk} s={s} flatDim={N}")
