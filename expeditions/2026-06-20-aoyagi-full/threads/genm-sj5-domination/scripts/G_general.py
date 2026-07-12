import numpy as np
# General test: is G(w, Z_deep) BOUNDED in the tail degeneration for the hard cases?
# b=1 throughout (corank ROW block one row). a, M2, Mlast general. Tail Z_deep = M2 x Mlast
# with singular values sigmas (one or two driven ->0 to test 1st/2nd-order-ish tail drops).
# A_cor: 1 x M2 box.  Q_b = A_cor Z_deep (1 x Mlast).  tau=||Q_b||.
# Freed corner Gamma: a x 1 (=a-vector).  loss = w + ||c0 + outer(Gamma, Qb)||^2 ; c0 a x Mlast const.
#  ||c0 + Gamma Qb||^2 = sum_{i,l}(c0[i,l]+Gamma[i]*Qb[l])^2.
# G = ∫_{A_cor box} [ ∫_{Gamma box} loss^{-cp} dGamma ] dA_cor.

rng=np.random.default_rng(3)
def build_Zdeep(M2, Mlast, sigmas):
    # Z_deep = U diag(sigmas) V^T,  U:M2xM2, V:Mlast x M2 (columns orthonormal) - random orth
    A=rng.standard_normal((M2,M2)); U,_=np.linalg.qr(A)
    B=rng.standard_normal((Mlast,M2)); V,_=np.linalg.qr(B)   # V: Mlast x M2, orthonormal cols
    S=np.diag([sigmas[i] for i in range(M2)])                # M2 x M2
    return U@S@V.T   # (M2xM2)(M2xM2)(M2xMlast) = M2 x Mlast

def Iga(w, Qb, a, cp, NG=25):
    # ∫_{Gamma in [-1,1]^a} (w + ||c0 + outer(Gamma,Qb)||^2)^{-cp} dGamma  (a-dim grid)
    Mlast=Qb.shape[0]
    c0=0.3*np.ones((a,Mlast))
    grids=np.meshgrid(*([np.linspace(-1,1,NG)]*a), indexing='ij')
    G=np.stack([g.ravel() for g in grids],axis=1)  # (NG^a, a)
    # loss for each Gamma: w + sum_{i,l}(c0[i,l]+G[:,i]*Qb[l])^2
    outer = G[:,:,None]*Qb[None,None,:]        # (Npts, a, Mlast)
    resid = c0[None,:,:] + outer
    loss = w + (resid**2).sum(axis=(1,2))
    vals = loss**(-cp)
    h=(2.0/(NG-1))**a
    return vals.sum()*h

def G_of(w, Z, a, cp, Ncor=60):
    M2=Z.shape[0]
    # integrate A_cor over [-1,1]^M2 (grid)
    axes=[np.linspace(-1,1,Ncor)]*M2
    grids=np.meshgrid(*axes,indexing='ij')
    Ac=np.stack([g.ravel() for g in grids],axis=1)   # (Ncor^M2, M2)
    Qb_all = Ac @ Z                                  # (Npts, Mlast)
    hcor=(2.0/(Ncor-1))**M2
    tot=0.0
    for k in range(Qb_all.shape[0]):
        tot += Iga(w, Qb_all[k], a, cp)
    return tot*hcor

def test(name, a, M2, Mlast, cp, w, sgs_list):
    print(f"[{name}] a={a} b=1 M2={M2} Mlast={Mlast} cp={cp} w={w}:  G vs tail singular value(s)")
    Gs=[]
    for sgs in sgs_list:
        Z=build_Zdeep(M2,Mlast,sgs)
        Gs.append(G_of(w,Z,a,cp))
    Gs=np.array(Gs)
    labels=[f"sg={s}" for s in sgs_list]
    print("   "+"  ".join(f"{l}:{g:.4e}" for l,g in zip(labels,Gs)))
    # slope of logG vs log(smallest sigma)
    small=np.array([min(s) for s in sgs_list])
    sl=np.diff(np.log(Gs))/np.diff(np.log(small))
    print(f"   d logG / d log(sigma_min) = {np.array2string(sl,precision=3)}   (BOUNDED if ->0; DIVISOR if <0 const)")

# Anchor sanity a=1,M2=2,Mlast=2 (expect bounded)
test("anchor 3322", 1,2,2, 1.8, 0.05, [[1.0,0.1],[1.0,1e-2],[1.0,1e-3],[1.0,1e-4]])
# (3,2,2,3): a=2,M2=2,Mlast=3 : the a>=M2 case  (carrierThr=2 => cp up to 2; e=cp-ab/2=cp-1)
test("3223 a>=M2", 2,2,3, 1.9, 0.05, [[1.0,0.1],[1.0,1e-2],[1.0,1e-3],[1.0,1e-4]])
# deeper first-order but wider: a=1,M2=3,Mlast=3
test("wide a=1 M2=3", 1,3,3, 1.8, 0.05, [[1.0,1.0,0.1],[1.0,1.0,1e-2],[1.0,1.0,1e-3],[1.0,1.0,1e-4]])
