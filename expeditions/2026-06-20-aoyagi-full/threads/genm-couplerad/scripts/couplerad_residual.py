import numpy as np
from scipy import integrate
# Verify: int_{B~ in [-1,1]^{ub}} (c + ||B~ Qb||^2)^{-q} dB~  ~  C * c^{ub/2 - q}  (2q>ub),  bounded (2q<=ub)
# uniform in c; depends on (E,Y) only through c = frobSq(EY). Compose with RectSchurCore at exponent q-ub/2.
def Bint(c, q, u, b, Qb):
    # ||B~ Qb||^2 = sum_rows (row . QbQb^T . row); B~ is u x b. Integrate over [-1,1]^{u*b}.
    G = Qb@Qb.T  # b x b PD
    # per-row separable: int over row in [-1,1]^b of (c_row + row G row^T)^-q ... not separable across rows (shared c).
    # do it by MC (uniform on cube), scaled.
    N=200000; rng=np.random.default_rng(0)
    B=rng.uniform(-1,1,(N,u,b))
    val=np.einsum('nij,jk,nik->ni',B,G,B).sum(axis=1)  # ||B~Qb||^2 per sample
    integrand=(c+val)**(-q)
    vol=2.0**(u*b)
    return integrand.mean()*vol

np.random.seed(0)
for (u,b,q,tag) in [(1,1,1.5,"ub=1,2q=3>1"),(2,1,2.0,"ub=2,2q=4>2"),(1,2,2.5,"ub=2,2q=5>2"),(2,1,0.4,"ub=2,2q=0.8<2 BOUNDED")]:
    ub=u*b
    Qb=np.random.randn(b, b+1)
    cs=np.array([1e-1,1e-2,1e-3,1e-4])
    vals=np.array([Bint(c,q,u,b,Qb) for c in cs])
    # fit exponent: log val vs log c
    slope=np.polyfit(np.log(cs),np.log(vals),1)[0]
    pred=ub/2-q
    print(f"{tag}: measured slope(logval/logc)={slope:+.3f}  predicted ub/2-q={pred:+.3f}  match={abs(slope-max(pred,0)*0 - (pred if 2*q>ub else 0))<0.15 if 2*q>ub else (abs(slope)<0.15)}")
    if 2*q<=ub: print(f"    2q<=ub: vals={vals} -> {'BOUNDED (slope~0)' if abs(slope)<0.15 else 'NOT bounded?!'}")
    else: print(f"    2q>ub: vals ~ c^({slope:.2f}), predicted c^({pred:.2f})")
