"""
At j=r (min(a,b)=0) examine the incidence-chart block dimensions to show a block VANISHES,
and check the scope hyp a+b<=M2 vs the actual object.
Blocks (incidence-cert Sec.1/3):  Qp: u x M2 (pivot);  Qb=A_cor: b x M2 (corank);
  transverse-Schur C rows: a rows;  minor D in GL_b;  W=Qp*N: u x d, d=M2-b (incidence coord).
Front pivot term dim 'ub';  transverse Schur active dirs 'M0*l' (l=rank W).
"""
from itertools import product
from functools import lru_cache
def redchain(t,M): return (t,)+tuple(M[2:])
@lru_cache(maxsize=None)
def minadm(M):
    n=len(M)
    if n==1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minadm(redchain(t,M)) for t in range(min(M[0],M[1])+1))
def argmin_t(M):
    best=None;bt=None
    for t in range(min(M[0],M[1])+1):
        v=(M[0]-t)*(M[1]-t)+minadm(redchain(t,M))
        if best is None or v<best: best=v;bt=t
    return bt

both_empty=0; b_empty=0; a_empty=0; neither=0
ub_zero=0
examples={"b=0":None,"a=0":None}
for nw in (3,4,5):
    for M in product(range(1,7),repeat=nw):
        M=tuple(M); ts=argmin_t(M); r=min(M[0]-ts,M[1]-ts)
        if r<1: continue
        u=ts+r; a=M[0]-u; b=M[1]-u
        assert min(a,b)==0
        d=M[2]-b
        ub=u*b
        if a==0 and b==0: both_empty+=1
        elif b==0: b_empty+=1; 
        elif a==0: a_empty+=1
        else: neither+=1
        if ub==0: ub_zero+=1
        if b==0 and examples["b=0"] is None: examples["b=0"]=(M,ts,r,u,a,b,d,"Qb rows=b=%d (EMPTY), detGram absent, W=Qp*N N=I_%d so W=Qp, shear B in R^{%dx0} vacuous"%(b,d,M[0]))
        if a==0 and b!=0 and examples["a=0"] is None: examples["a=0"]=(M,ts,r,u,a,b,d,"C rows=a=0 (no transverse Schur), detGram det^0=unit; pivot block ub=%d"%ub)

print("j=r cases: both a=b=0:",both_empty," b=0 only:",b_empty," a=0 only:",a_empty," neither(SHOULD BE 0):",neither)
print("cases with ub=u*b=0 (front pivot term vanishes):",ub_zero)
print()
print("b=0 witness:",examples["b=0"])
print("a=0 witness:",examples["a=0"])
