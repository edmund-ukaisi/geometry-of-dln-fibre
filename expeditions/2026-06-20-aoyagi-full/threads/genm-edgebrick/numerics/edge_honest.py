import numpy as np
rng = np.random.default_rng(1)
# Edge case: a=2, b=2, rho=3 (edge a=rho-b+1=2). Z: 3xn rank-3 fixed. K=A_cor·Z (b×n). c'>ab/2=2.
a,b,rho,n = 2,2,3,3
Zfix = np.array([[1.0,0,0],[0,1.0,0],[0,0,1.0]])   # rho×n, rank rho
c = 2.4                                             # c' just above ab/2=2 ; reduction target c'-ab/2=0.4
w  = 0.01                                            # small pivot floor (coupled term would be here)

def frobsq(M): return float(np.sum(M*M))

def gamma_integral_box(Ccross, K, NG=20000, box=1.0):
    """∫_{Γ∈[-box,box]^{a×b}} (w + frobSq(Ccross+Γ·K))^{-c} dΓ   (MC, box-restricted)"""
    G = rng.uniform(-box,box,size=(NG,a,b))
    val = 0.0
    E = Ccross[None,:,:] + np.einsum('gij,jk->gik', G, K)
    loss = w + np.sum(E*E,axis=(1,2))
    return (2*box)**(a*b) * np.mean(loss**(-c))

def gamma_integral_gauss(Ccross, K, NG=20000, sig=3.0):
    """proxy for univ-Γ (wide Gaussian, importance-weighted): the det-charge route"""
    G = rng.normal(0,sig,size=(NG,a,b))
    E = Ccross[None,:,:] + np.einsum('gij,jk->gik', G, K)
    loss = w + np.sum(E*E,axis=(1,2))
    wgt  = np.exp(np.sum(G*G,axis=(1,2))/(2*sig**2)) * (sig*np.sqrt(2*np.pi))**(a*b)
    return np.mean(loss**(-c) * wgt)

def outer(NA=6000, delta=0.0, Cscale=1.0, mode='box'):
    """∫_{A_cor∈box, det(KKt)>delta} [Γ-integral] dA_cor ; refine delta→0 to test convergence."""
    tot=0.0; cnt=0
    for _ in range(NA):
        A = rng.uniform(-1,1,size=(b,rho))         # A_cor  b×rho
        K = A @ Zfix                                # b×n
        d = np.linalg.det(K@K.T)
        if d<=delta: continue
        Ccross = Cscale*rng.uniform(-1,1,size=(a,n))
        gi = gamma_integral_box(Ccross,K,NG=3000) if mode=='box' else gamma_integral_gauss(Ccross,K,NG=3000)
        tot += gi; cnt+=1
    vol=2.0**(b*rho)
    return vol*tot/NA   # includes the (skipped => 0) mass, so ×(cnt/NA) implicitly via /NA

print(f"a={a} b={b} rho={rho}  EDGE (a=rho-b+1={rho-b+1})  c'={c}  ab/2={a*b/2}")
print("\n[BOX-restricted Γ, generic Ccross]  refine det-cutoff δ→0:")
for delta in [0,1e-3,1e-4,1e-5,1e-6]:
    print(f"   δ={delta:.0e} :  outer ≈ {outer(NA=8000,delta=delta,mode='box'):10.3f}")
print("\n[Gaussian(univ-proxy) Γ, generic Ccross]  refine det-cutoff δ→0 (the det-charge route):")
for delta in [0,1e-3,1e-4,1e-5,1e-6]:
    print(f"   δ={delta:.0e} :  outer ≈ {outer(NA=8000,delta=delta,mode='gauss'):10.3f}")
