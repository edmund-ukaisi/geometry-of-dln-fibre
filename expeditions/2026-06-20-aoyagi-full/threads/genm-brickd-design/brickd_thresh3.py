import numpy as np
from scipy.special import erf
from math import gamma as G_
rng=np.random.default_rng(3)

u,a,b=1,1,2; p,r=u+a,u+b; n,n0=3,3
xs=np.linspace(-16,20,280); ss=np.exp(xs); dx=xs[1]-xs[0]
cprimes=[1.5,2.0,2.3,2.5,2.7,3.0]
spow={c: ss**c for c in cprimes}
def Efun(w):
    w=np.maximum(w,1e-300); return np.sqrt(np.pi/w)*erf(np.sqrt(w))
def eigs_hsQ(N):
    z=rng.uniform(-1,1,size=(N,u,n)); Ac=rng.uniform(-1,1,size=(N,b,n0))
    hsQ=np.concatenate([z,Ac],axis=1); Gm=hsQ@np.transpose(hsQ,(0,2,1))
    return np.clip(np.linalg.eigvalsh(Gm),0,None)
vol=2.0**(u*n+b*n0)
def run(N):
    lam=eigs_hsQ(N)
    out={c:np.zeros(N) for c in cprimes}
    for j,s in enumerate(ss):
        prod=np.ones(N)
        for i in range(r): prod*=Efun(s*lam[:,i])**p
        for c in cprimes: out[c]+=spow[c][j]*prod*dx
    res={}
    for c in cprimes:
        g=out[c]/G_(c); res[c]=(g.mean()*vol, np.sort(g)[::-1][:5].sum()/max(g.sum(),1e-300))
    return res
print(f"u={u},a={a},b={b}; ab/2={a*b/2}; predicted T2=2.5 (minAdm_red=3, reduced RLCT=1.5)")
r1=run(60_000); r2=run(240_000)
for c in cprimes:
    v1=r1[c][0]; v2=r2[c][0]; top=r2[c][1]
    print(f" c'={c:4.2f}: I(6e4)={v1:.3e} I(2.4e5)={v2:.3e} ratio={v2/max(v1,1e-300):5.2f} top5frac={top:.3f}")
