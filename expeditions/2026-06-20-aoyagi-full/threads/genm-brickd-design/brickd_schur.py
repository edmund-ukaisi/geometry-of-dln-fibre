import numpy as np
rng=np.random.default_rng(2)
# (1) Verify Codex Q2 Schur identity: det(G)=det(Q_p Q_p^T)·det(Q_b(I-Pi_p)Q_b^T), G=[Q_p;Q_b][...]^T.
for _ in range(3):
    u,b,n=2,2,4
    Qp=rng.standard_normal((u,n)); Qb=rng.standard_normal((b,n))
    hsQ=np.vstack([Qp,Qb]); G=hsQ@hsQ.T
    Pi_p=Qp.T@np.linalg.inv(Qp@Qp.T)@Qp          # proj onto rowspan Qp
    schur=Qb@(np.eye(n)-Pi_p)@Qb.T
    lhs=np.linalg.det(G); rhs=np.linalg.det(Qp@Qp.T)*np.linalg.det(schur)
    print(f" Schur identity: det(G)={lhs:.5f}  det(QpQp^T)det(schur)={rhs:.5f}  match={np.isclose(lhs,rhs)}")

# (2) det-Gram A_cor integral threshold via convergence test (robust):
#     ∫_{A_cor box} det(A_cor Z (A_cor Z)^T)^{-s} dA_cor  finite for s< ? .  Charge s=a/2 must be affordable.
def detgram_conv(b,n,n0,s,N):
    Z=rng.standard_normal((n0,n))
    Ac=rng.uniform(-1,1,size=(N,b,n0)); Qb=Ac@Z; G=Qb@np.transpose(Qb,(0,2,1))
    det=np.abs(np.linalg.det(G)); val=np.maximum(det,1e-300)**(-s)
    return val.mean()*2.0**(b*n0), np.sort(val)[::-1][:5].sum()/max(val.sum(),1e-300)
print("\ndet-Gram integral ∫det^{-s}: finite? (stable across N & small top5 => finite)")
for (b,n,n0) in [(2,3,3),(2,4,4)]:
    print(f" b={b},n={n},n0={n0}:")
    for s in [0.5,1.0,1.5,2.0]:
        v1,_=detgram_conv(b,n,n0,s,200_000); v2,top=detgram_conv(b,n,n0,s,800_000)
        print(f"   s={s:4.2f}: I={v2:.3e} ratio={v2/max(v1,1e-300):5.2f} top5={top:.3f}  (charge a/2 for a=1 is 0.5; a=2 is 1.0)")
