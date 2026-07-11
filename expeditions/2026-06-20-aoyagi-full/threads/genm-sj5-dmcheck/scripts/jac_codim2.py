"""
Corrected Jacobian-codim check for DOUBLE-bottleneck chains: the {rank<=rho} variety is a UNION of
components (which factor drops), of different codims; cCodim = MIN.  The pushforward tube MEASURE is
dominated by the SMALLEST-codim component.  Confirm the cheapest component's codim = cCodim by
forcing the CHEAPEST factor to drop, not always the first.
"""
import numpy as np, itertools
from functools import lru_cache

@lru_cache(None)
def cCodim(c,rho):
    c=tuple(c); L=len(c)-1
    if L==0: return 0
    if L==1:
        r=min(rho,c[0],c[1]); return (c[0]-r)*(c[1]-r)
    best=None; rng=range(0,max(c)+1)
    for T in itertools.product(rng,repeat=L):
        if any(T[i]<T[i+1] for i in range(L-1)): continue
        if T[0]>min(c[0],c[1]): continue
        if T[-1]>rho: continue
        if not all(T[j]<=min(T[j-1],c[j+1]) for j in range(1,L)): continue
        val=(c[0]-T[0])*(c[1]-T[0])+sum((T[j-1]-T[j])*(c[j+1]-T[j]) for j in range(1,L))
        if best is None or val<best: best=val
    return best if best is not None else 0

def jac_codim_dropfactor(c, rho, drop_idx, drop_rank, seed=0, ntrial=5):
    """Sit on the component where factor `drop_idx` has rank drop_rank (others generic).
       Return numeric Jacobian rank of (rho+1)-minors of the whole product."""
    L=len(c)-1
    best=None
    for tr in range(ntrial):
        rng=np.random.default_rng(1000*seed+tr)
        facs=[rng.standard_normal((c[i],c[i+1])) for i in range(L)]
        r=drop_rank
        U=rng.standard_normal((c[drop_idx],r)); V=rng.standard_normal((r,c[drop_idx+1]))
        facs[drop_idx]=U@V
        def minors_vec(flat):
            k=0; fs=[]
            for i in range(L):
                sz=c[i]*c[i+1]; fs.append(flat[k:k+sz].reshape(c[i],c[i+1])); k+=sz
            P=fs[0]
            for M in fs[1:]: P=P@M
            rows=list(itertools.combinations(range(c[0]),rho+1)); cols=list(itertools.combinations(range(c[-1]),rho+1))
            return np.array([np.linalg.det(P[np.ix_(rr,cl)]) for rr in rows for cl in cols])
        flat0=np.concatenate([f.ravel() for f in facs]); m0=minors_vec(flat0)
        if np.max(np.abs(m0))>1e-6: continue
        n=len(flat0); eps=1e-6; J=np.zeros((len(m0),n))
        for j in range(n):
            d=flat0.copy(); d[j]+=eps; J[:,j]=(minors_vec(d)-m0)/eps
        rk=np.linalg.matrix_rank(J,tol=1e-4)
        best=rk if best is None else min(best,rk)   # cheapest achievable at this component
    return best

# double bottleneck: try dropping EACH factor to reach rank<=rho, take min codim over choices
def geom_cCodim(c, rho, seed=0):
    L=len(c)-1; cands=[]
    for di in range(L):
        # forcing factor di to rank dr makes product rank <= min(dr, other caps).
        for dr in range(0, min(c[di],c[di+1])+1):
            # only if this forces product rank <= rho
            # product rank <= min over all factor ranks along the chain; with factor di at dr,
            # product rank <= dr (roughly); require dr <= rho
            if dr<=rho:
                jc=jac_codim_dropfactor(c,rho,di,dr,seed)
                if jc is not None: cands.append((di,dr,jc))
    return cands

print("Double/triple-bottleneck: geometric codim of CHEAPEST component vs cCodim (MIN over components):")
for c,rho in [((4,2,2,4),1),((4,2,4,2,4),1),((2,5,2,2,5),1),((7,2,2,2,7),1),((5,2,2,5),1)]:
    cc=cCodim(c,rho)
    cands=geom_cCodim(c,rho,seed=3)
    mn=min(x[2] for x in cands) if cands else None
    print(f"chain={str(c):16} rho={rho} cCodim(profile)={cc}  geom cheapest-component codim={mn}  "
          f"match={mn==cc}   [components (drop_factor,rank,codim): {cands}]")
