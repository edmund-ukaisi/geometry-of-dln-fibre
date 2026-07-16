import itertools
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
# for binding cuts (a>=1,b>=1), tabulate a+b - rho (rho=tailMinWidth=min(M[1:]))
from collections import Counter
c=Counter()
for Lp in [3,4]:
  for M in itertools.product(range(1,7),repeat=Lp):
    mA=minAdm(M); rho=min(M[1:])
    for t in range(1,min(M[0],M[1])+1):
        a,b=M[0]-t,M[1]-t
        if a<1 or b<1: continue
        if a*b+minAdm((t,)+M[2:])==mA:   # binding
            c[a+b-rho]+=1
print("distribution of (a+b - rho) over BINDING cuts with a,b>=1:")
for k in sorted(c): print(f"   a+b-rho = {k:+d}: {c[k]} binding cuts  {'<-- INTERIOR (front charge OK)' if k<=0 else ('<-- EDGE (my {Gamma=0})' if k==1 else '<-- DEEPER (beyond edge!)')}")
