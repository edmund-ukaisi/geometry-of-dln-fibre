import numpy as np
rng=np.random.default_rng(0)
def frob2(X): return float(np.sum(X*X))
# ---- (I) R1 identity: E_top+E_tr = frobSq(E·Y)+frobSq(B̃·Q_b) ----
def check_R1(u,a,b,n):
    Qinl=rng.standard_normal((u,n)); Qb=rng.standard_normal((b,n))
    P=rng.standard_normal((u,u))
    while abs(np.linalg.det(P))<1e-3: P=rng.standard_normal((u,u))
    B12=rng.standard_normal((u,b)); C=rng.standard_normal((a,u))
    G=Qb@Qb.T; Gi=np.linalg.inv(G); Pi=np.eye(n)-Qb.T@Gi@Qb
    Qtil=Qinl+np.linalg.inv(P)@B12@Qb
    Etop=frob2(P@Qtil); Etr=frob2(C@Qtil@Pi)
    Y=Qinl@Pi; Az=Qinl@Qb.T@Gi; Bt=B12+P@Az; E=np.vstack([P,C])
    final=abs((Etop+Etr)-(frob2(E@Y)+frob2(Bt@Qb)))
    return final
print("(I) R1 identity  E_top+E_tr = frobSq(E·Y)+frobSq(B̃·Q_b)  (err ~0):")
for (u,a,b,n) in [(3,1,1,4),(2,1,2,5),(4,2,1,6),(2,2,3,6),(3,2,2,5)]:
    print(f"   (u,a,b,n)={(u,a,b,n)}: final err = {check_R1(u,a,b,n):.2e}")

# ---- (II) CHARGE CRUX: over the BOX, the B₁₂-integral stays BOUNDED as Q_b→degenerate (NO det^{-u/2} stacking) ----
# vs the UNBOUNDED (ℝ) version which WOULD scale as det(Q_bQ_bᵀ)^{-u/2}.
def box_B12_integral(u,b,n,q, Qinl,Qb,P,kappa, N=300000):
    # ∫_{B12∈[-1,1]^{ub}} (frobSq(P·Qinl + B12·Qb) + kappa)^{-q} dB12   [MC over box]
    B=rng.uniform(-1,1,(N,u,b))
    base=P@Qinl
    val=np.array([frob2(base + B[i]@Qb) for i in range(0,N,50)])  # subsample for speed
    integrand=(val+kappa)**(-q)
    return integrand.mean()*(2.0**(u*b))
print("\n(II) CHARGE CRUX: boxed ∫_{B12}(frobSq(P·Qinl+B12·Qb)+κ)^{-q}dB12 as Q_b→0 (scale ε), z0/Qinl FIXED (κ floor>0):")
u,b,n,q=3,1,4,2.5; a=1
Qinl0=rng.standard_normal((u,n)); Qb0=rng.standard_normal((b,n)); P=rng.standard_normal((u,u))
kappa=0.5  # E_tr-type floor, fixed (z0≠0)
print(f"   u={u} b={b} ub={u*b}  frobSq(P·Qinl)={frob2(P@Qinl0):.3f} (the z0-floor, >0)")
for eps in [1.0,1e-1,1e-2,1e-3,1e-4]:
    Qb=eps*Qb0; G=Qb@Qb.T
    boxed=box_B12_integral(u,b,n,q,Qinl0,Qb,P,kappa)
    detpow=np.linalg.det(G)**(-u/2)  # what the UNBOUNDED (Gaussian) version would scale as
    print(f"   ε={eps:.0e}: BOXED ∫ = {boxed:8.4f}   |  det(Q_bQ_bᵀ)^(-u/2) = {detpow:.3e}  (unbounded-ℝ scaling)")
print("   => BOXED ∫ stays BOUNDED (→(2^ub)(frobSq(P·Qinl)+κ)^{-q}) while det^{-u/2}→∞.")
print("   => the u/2 does NOT stack with the charge over the box; it's z0-tied (needs frobSq(P·Qinl)→0 too). CHARGE = a/2 pure.")
