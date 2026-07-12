import numpy as np, sys
rng=np.random.default_rng(0)
def pr(*a): print(*a); sys.stdout.flush()

pr("="*68)
pr("(1) Gram-Schmidt det product  det(QQᵀ)=∏‖q_i^⊥‖²  (numeric, many b,n)")
pr("="*68)
def gs_perp_sq(Q):
    b=Q.shape[0]; basis=[]; out=[]
    for i in range(b):
        v=Q[i].astype(float).copy()
        for u in basis: v=v-(u@Q[i])/(u@u)*u
        out.append(v@v); basis.append(v)
    return np.array(out)
maxerr=0
for b,n in [(2,3),(3,4),(3,5),(4,6),(5,7)]:
    for _ in range(200):
        Q=rng.standard_normal((b,n))
        lhs=np.linalg.det(Q@Q.T); rhs=np.prod(gs_perp_sq(Q))
        maxerr=max(maxerr,abs(lhs-rhs)/max(abs(lhs),1e-9))
pr(f"  det(QQᵀ)=∏‖q_i^⊥‖²  max rel err over 1000 draws = {maxerr:.2e}  (identity holds)")

pr("")
pr("="*68)
pr("(2) innermost row integral: ‖q_b^⊥‖² = frobSq(A_b·(ZΠ))  (SPEC shape)")
pr("="*68)
maxd=0
for _ in range(300):
    M2,n,b=4,5,3
    Z=rng.standard_normal((M2,n)); A=rng.standard_normal((b,M2)); Q=A@Z
    V=Q[:b-1]; P_V=V.T@np.linalg.pinv(V@V.T)@V; Pi=np.eye(n)-P_V
    qbp=Q[b-1]-Q[b-1]@P_V
    maxd=max(maxd,abs(qbp@qbp-np.linalg.norm(A[b-1]@(Z@Pi))**2))
pr(f"  ‖q_b^⊥‖² vs frobSq(A_b·ZΠ): max abs diff over 300 = {maxd:.2e}  (equal ⇒ SPEC m=1,tail=ZΠ)")

pr("")
pr("="*68)
pr("(3) ENTANGLEMENT: SPEC leaves sigMin(ZΠ)^{-α'}; ZΠ depends on OUTER rows")
pr("="*68)
M2,n,b=4,6,3; Z=rng.standard_normal((M2,n)); vals=[]
for _ in range(6):
    Ao=rng.standard_normal((b-1,M2)); V=Ao@Z
    P_V=V.T@np.linalg.pinv(V@V.T)@V; ZPi=Z@(np.eye(n)-P_V)
    s=np.linalg.svd(ZPi,compute_uv=False); vals.append(s[s>1e-9].min())
pr(f"  sigMin(ZΠ) across 6 outer-row draws: {[f'{v:.3f}' for v in vals]}")
pr(f"  spread {min(vals):.3f}..{max(vals):.3f}  ⇒ the residual sigMin factor is NOT constant;")
pr("  the outer-row integral must carry sigMin(ZΠ)^{-α'} ⊗ ‖q_i^⊥‖^{-a} jointly (not a clean 2nd SPEC).")
