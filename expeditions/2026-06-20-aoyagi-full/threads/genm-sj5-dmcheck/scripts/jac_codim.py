"""
Independent check that the GEOMETRIC product-tube codim = cCodim (the D_q side of no-collapse),
for BOTTLENECK products.  Method: Jacobian rank of the (rho+1)-minor ideal of the product map at a
generic rank-rho point.  codim of {rank <= rho} = rank of the Jacobian of the generating minors
(the variety is smooth of that codim at a generic point; radical determinantal => reduced).
Compare to cCodim (profile enumeration) and the free-matrix determinantal codim.
"""
import sympy as sp, itertools, random
from functools import lru_cache

@lru_cache(None)
def minAdm(M):
    M=tuple(M)
    if len(M)<=1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
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

def product_of_chain(c, seed=0):
    """Symbolic product P = A0 A1 ... of chain c=(n0,...,nk), with generic INTEGER entries EXCEPT
       we keep the LAST factor symbolic to probe transversality; here keep ALL symbolic small."""
    rng=random.Random(seed)
    mats=[]; syms=[]
    for i in range(len(c)-1):
        r,cc=c[i],c[i+1]
        M=sp.zeros(r,cc)
        for a in range(r):
            for b in range(cc):
                s=sp.Symbol(f'x_{i}_{a}_{b}')
                M[a,b]=s; syms.append(s)
        mats.append(M)
    P=mats[0]
    for M in mats[1:]: P=P*M
    return P, syms

def jac_codim_at_generic(c, rho, seed=0, trials=3):
    """codim{rank P <= rho} via Jacobian rank of (rho+1)-minors at a generic rank-rho point.
       Build a rank-rho point by substituting one factor to have rank rho, others generic; then
       evaluate the Jacobian of all (rho+1)-minors and take its rank => codim (smooth pt)."""
    P, syms = product_of_chain(c, seed)
    n0, nk = c[0], c[-1]
    if rho+1 > min(n0,nk):
        return 0
    # all (rho+1)-minors
    rows=list(itertools.combinations(range(n0), rho+1))
    cols=list(itertools.combinations(range(nk), rho+1))
    minors=[P[list(r),list(cl)].det() for r in rows for cl in cols]
    best=0
    for tr in range(trials):
        rng=random.Random(1000*seed+tr)
        # generic rank-rho point: set factor entries so partial products have rank rho.
        # Easiest generic construction: random integer values, then RESTRICT to a rank-rho locus by
        # forcing the product to rank rho via choosing the middle-most factor rank rho.  Instead,
        # sample random values and PROJECT: we just want a point ON {rank<=rho}. Construct explicitly:
        subs={}
        # assign generic values
        for s in syms: subs[s]=sp.Rational(rng.randint(-4,4))
        # force rank <= rho by zeroing enough of the NARROWEST factor's rows/cols is messy;
        # instead build P0 as an explicit rank-rho matrix and solve — too hard symbolically.
        # Pragmatic: evaluate Jacobian at a random point and check the minors are ~0 by construction
        # only when we truly sit on the locus. Use a direct rank-rho product construction:
        pass
    # Direct construction: P0 = U * S * V with S rank rho, then perturb in factor space numerically.
    return None

# ---- numeric Jacobian-rank codim (robust) ----
import numpy as np
def numeric_jac_codim(c, rho, seed=0, ntrial=6):
    """Sample a generic point ON {rank(product)<=rho}: force one factor to rank rho.
       Then numerically compute rank of Jacobian of (rho+1)-minors wrt ALL factor entries."""
    rng=np.random.default_rng(seed)
    L=len(c)-1
    codims=[]
    for _ in range(ntrial):
        # build factors; to sit on {rank<=rho}, pick the factor with smallest output dim and
        # give the WHOLE product rank rho by making the first factor rank rho (thin).
        facs=[rng.standard_normal((c[i],c[i+1])) for i in range(L)]
        # force product rank <= rho: replace facs[0] by a rank-rho matrix (its col space dim rho)
        r0=min(rho,c[0],c[1])
        U=rng.standard_normal((c[0],r0)); V=rng.standard_normal((r0,c[1]))
        facs[0]=U@V
        # symbolic Jacobian is heavy; use finite-difference rank of the minor map
        def minors_vec(flat):
            k=0; fs=[]
            for i in range(L):
                sz=c[i]*c[i+1]; fs.append(flat[k:k+sz].reshape(c[i],c[i+1])); k+=sz
            P=fs[0]
            for M in fs[1:]: P=P@M
            rows=list(itertools.combinations(range(c[0]),rho+1))
            cols=list(itertools.combinations(range(c[-1]),rho+1))
            return np.array([np.linalg.det(P[np.ix_(r,cl)]) for r in rows for cl in cols])
        flat0=np.concatenate([f.ravel() for f in facs])
        m0=minors_vec(flat0)
        if np.max(np.abs(m0))>1e-6:  # not on locus; skip
            continue
        # finite-diff Jacobian
        n=len(flat0); eps=1e-6
        J=np.zeros((len(m0),n))
        for j in range(n):
            d=flat0.copy(); d[j]+=eps
            J[:,j]=(minors_vec(d)-m0)/eps
        codims.append(np.linalg.matrix_rank(J,tol=1e-4))
    return max(codims) if codims else None

print("GEOMETRIC (Jacobian-rank) codim of {rank(product)<=rho} vs cCodim vs free-determinantal:")
print(f"{'chain':16}{'rho':>4}{'cCodim':>8}{'jacCodim':>10}{'free':>7}")
cases=[((4,2,4),1),((5,2,5),1),((3,3,4),1),((3,3,4),2),((2,4,2,5),1),((4,2,4,2,4),1),
       ((3,1,3),0),((4,2,2,4),1),((3,3,3,4),2)]
for c,rho in cases:
    cc=cCodim(c,rho)
    jc=numeric_jac_codim(c,rho,seed=7)
    n0,nk=c[0],c[-1]; r=min(rho,n0,nk); free=(n0-r)*(nk-r)
    print(f"{str(c):16}{rho:>4}{cc:>8}{str(jc):>10}{free:>7}")
