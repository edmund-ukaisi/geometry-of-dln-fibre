import numpy as np
rng=np.random.default_rng(0)
# Test: multiplier M=∫_Y(g^2+||YB||^2)^{-a/2}dY, B FULL RANK (identity), Y dim d_Y.
# Predicted: bounded/log iff a <= d_Y ; power loss g^{d_Y-a} iff a > d_Y.
def M_fullrank(a, dY, g, N=3_000_000):
    Y=rng.uniform(-1,1,(N,dY))
    return ((g*g+(Y**2).sum(1))**(-a/2.0)).mean()*(2.0**dY)
def slope(gs,Ms): return np.polyfit(np.log(1/gs),np.log(Ms),1)[0]
gs=np.array([1e-1,1e-2,1e-3,1e-4,1e-5])
print("Full-rank B: M vs 1/g. slope 0=>bounded/log (a<=dY) ; slope=(a-dY)>0 => power g^{-(a-dY)}")
for a,dY in [(1,2),(2,2),(3,2),(4,2),(1,4),(4,4),(5,4),(8,8),(4,8)]:
    Ms=np.array([M_fullrank(a,dY,g) for g in gs])
    s=slope(gs,Ms)
    pred = "bounded" if a<dY else ("log(a=dY)" if a==dY else f"POWER g^-{a-dY}")
    print(f"  a={a}, d_Y={dY}: slope={s:+.3f}   predicted {pred}")

print("\n" + "="*60)
print("Do BINDING cuts ever violate a <= d_Y at ANY recursion level?")
print("="*60)
from functools import lru_cache
@lru_cache(None)
def minAdmRec(M):
    L=len(M)-1
    if L==0:return 0
    if L==1:return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def binding_cut(M):  # a binding t
    v=minAdmRec(M)
    for t in range(min(M[0],M[1])+1):
        if (M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:])==v: return t
    return None
def check_chain(M):
    """Recurse along a binding path; at each peel check a=(M0-t)(M1-t) vs d_Y=(M1-t)*M2."""
    M=tuple(M); bad=[]
    while len(M)-1>=2:
        t=binding_cut(M); a=(M[0]-t)*(M[1]-t); dY=(M[1]-t)*M[2]
        if a>dY: bad.append((M,t,a,dY))
        M=(t,)+M[2:]
    return bad
import itertools
viol=0; tot=0; examples=[]
for L in range(2,6):
  for M in itertools.product(range(1,5),repeat=L+1):
    tot+=1; b=check_chain(M)
    if b: viol+=1; examples+=b[:1]
print(f"chains checked (widths1..4, L=2..5): {tot}")
print(f"binding-path peels with a > d_Y (power loss => joint needed): {viol}")
for e in examples[:12]: print("   VIOLATION",e)
