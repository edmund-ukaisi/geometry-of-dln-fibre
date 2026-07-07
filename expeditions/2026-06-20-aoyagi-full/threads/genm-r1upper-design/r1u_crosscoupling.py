import numpy as np
rng=np.random.default_rng(0)
# Verify (1) the TRUE post-schur integrand identity and (2) the Γ-translation orthogonal split,
# for a MATRIX corank Γ (case (4,4,4,4) t=2: M0=M1=4, t=2, so A,Γ are 2x2, Q_b = 2 rows of Q (4×n)).
def check(M0,M1,t,n,trials=200):
    p=M0-t; q=M1-t                      # Γ is p×q ; Q_b is q×n
    maxerr_id=0.0; maxerr_tr=0.0; maxerr_orth=0.0
    for _ in range(trials):
        A=rng.standard_normal((t,t)); 
        while abs(np.linalg.det(A))<1e-3: A=rng.standard_normal((t,t))
        B=rng.standard_normal((t,q)); C=rng.standard_normal((p,t)); Gam=rng.standard_normal((p,q))
        Q=rng.standard_normal((M1,n))    # Q_p = top t rows, Q_b = bottom q rows (pivot col split)
        Qp=Q[:t]; Qb=Q[t:]
        D=Gam + C@np.linalg.inv(A)@B      # so that schur complement of [[A,B],[C,D]] is Gam
        A0=np.block([[A,B],[C,D]])
        lhs=(A0@Q); lhs=(lhs**2).sum()    # frobSq(A0 Q)
        Qtp=Qp + np.linalg.inv(A)@B@Qb    # Q̃_p
        rhs=((A@Qtp)**2).sum() + ((C@Qtp + Gam@Qb)**2).sum()   # controller's TRUE form
        maxerr_id=max(maxerr_id, abs(lhs-rhs))
        # (2) Γ-translation: Γ0 = C Q̃_p Q_b^+  (Q_b^+ = Q_bᵀ(Q_b Q_bᵀ)⁻¹, full row rank q)
        Gram=Qb@Qb.T
        if np.linalg.matrix_rank(Qb)==q:
            Qbpinv=Qb.T@np.linalg.inv(Gram)
            Gam0=(C@Qtp)@Qbpinv           # p×q
            Gpp=Gam+Gam0                   # translated Γ'' (integration var shift, Jac 1)
            # claim: ‖C Q̃_p + Γ Q_b‖² = ‖Γ'' Q_b‖² + ‖C Q̃_p (I - P_{Qb})‖²
            P=Qb.T@np.linalg.inv(Gram)@Qb  # n×n projection onto rowspace(Qb)
            resid=(C@Qtp)@(np.eye(n)-P)
            lhs2=((C@Qtp + Gam@Qb)**2).sum()
            rhs2=((Gpp@Qb)**2).sum() + (resid**2).sum()
            maxerr_tr=max(maxerr_tr, abs(lhs2-rhs2))
            # orthogonality: <Γ'' Q_b, resid> = 0
            maxerr_orth=max(maxerr_orth, abs((( Gpp@Qb)*resid).sum()))
    return maxerr_id, maxerr_tr, maxerr_orth

for (M0,M1,t,n,name) in [(2,2,1,2,"(2,2,2,2) t=1 [Γ 1×1]"),(4,4,2,4,"(4,4,4,4) t=2 [Γ 2×2]"),
                          (3,3,2,3,"(3,3,3,3) t=2 [Γ 1×1]"),(4,4,1,4,"(4,4,4,4) t=1 [Γ 3×3]")]:
    e1,e2,e3=check(M0,M1,t,n)
    print(f"{name}:")
    print(f"   max|frobSq(A0Q) - (‖A Q̃_p‖²+‖C Q̃_p+Γ Q_b‖²)| = {e1:.2e}   (0 => TRUE integrand identity ✓)")
    print(f"   max|‖CQ̃_p+ΓQ_b‖² - (‖Γ''Q_b‖²+‖CQ̃_p(I-P)‖²)| = {e2:.2e}   (0 => translation split ✓)")
    print(f"   max|<Γ''Q_b, CQ̃_p(I-P)>| = {e3:.2e}   (0 => orthogonality ✓)")
