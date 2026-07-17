import numpy as np, sympy as sp
np.random.seed(0)
print("="*70); print("PIVOT-TAIL obligation-1 CoV algebra checks"); print("="*70)
t,b,q = 2,2,4   # Q~p is t x q, P is t x t, B12 is t x b, Q_b is b x q, Q_p is t x q
a = 3           # corank width (Gram exponent a/2)
# (1) B12 -> B' = P^{-1} B12 Jacobian = |det P|^b  (map I_b (x) P^{-1})
P = np.random.randn(t,t); 
J_shear = abs(np.linalg.det(np.kron(np.eye(b), np.linalg.inv(P))))
print(f"(1) |det(I_b (x) P^-1)| = {J_shear:.5f}   |det P|^(-b) = {abs(np.linalg.det(P))**(-b):.5f}  match={np.isclose(J_shear, abs(np.linalg.det(P))**(-b))}")
# (2) Q~p = Q_p + P^-1 B12 Q_b == Q_p + B' Q_b
Qp=np.random.randn(t,q); B12=np.random.randn(t,b); Qb=np.random.randn(b,q)
Qtp = Qp + np.linalg.inv(P)@B12@Qb
Bp  = np.linalg.inv(P)@B12
print(f"(2) Q~p == Q_p + B' Q_b : {np.allclose(Qtp, Qp+Bp@Qb)}")
# (3) right-orthogonal V: Gram invariance
Vt,_=np.linalg.qr(np.random.randn(q,q))  # orthogonal q x q
print(f"(3) (Q~p V)(Q~p V)^T == Q~p Q~p^T : {np.allclose((Qtp@Vt)@(Qtp@Vt).T, Qtp@Qtp.T)}")
# (4) SVD-compress Q_b (rank b=2 full here): Q_b = Ub S Vb^T ; choose V = Vb so Q_b V = [Psi|0], Psi = Ub S (b x b)
Ub,sig,VbT = np.linalg.svd(Qb, full_matrices=True)   # Qb = Ub diag(sig) VbT, VbT is q x q
V = VbT.T                                            # q x q orthogonal
QbV = Qb@V
print(f"(4) Q_b V has zero last (q-b) cols: {np.allclose(QbV[:,b:],0)}   Psi=QbV[:,:b] shape={QbV[:,:b].shape}")
Psi = QbV[:,:b]   # b x b, invertible (full rank)
QtpV = Qtp@V
R1 = (Qp@V)[:,:b]; R2 = (Qp@V)[:,b:]
# Q~p V = [ (Qp V)_1 + B' Psi | (Qp V)_2 ] = [R1 + B' Psi | R2]
print(f"    Q~p V == [R1 + B' Psi | R2] : {np.allclose(QtpV, np.hstack([R1+Bp@Psi, R2]))}")
W = R1 + Bp@Psi   # t x b free (as B' free)
C0 = R2@R2.T      # t x t PSD shift
print(f"    Gram(Q~p) == W W^T + C0 : {np.allclose(Qtp@Qtp.T, W@W.T + C0)}")
# (5) B'->W=R1+B'Psi Jacobian |det Psi|^t
J_W = abs(np.linalg.det(np.kron(Psi.T, np.eye(t))))   # map on t x b : B' -> B'Psi
print(f"(5) |det(map B'->B'Psi)| = {J_W:.5f}   |det Psi|^t = {abs(np.linalg.det(Psi))**t:.5f}  match={np.isclose(J_W, abs(np.linalg.det(Psi))**t)}")
# (6) determinant PSD-shift dominance: det(WW^T + C0) >= det(WW^T)  (so ^(-a/2) <= )
vals=[]
for _ in range(2000):
    Wr=np.random.randn(t,b); C=np.random.randn(t,t); C=C@C.T
    vals.append(np.linalg.det(Wr@Wr.T + C) >= np.linalg.det(Wr@Wr.T)-1e-9)
print(f"(6) det(WW^T+C0)>=det(WW^T) over 2000 PSD C0: {all(vals)}")
print()
print("="*70); print("obligation-2: deeper-strata gate |det Psi|^{-t} blows up as rank Q_b drops"); print("="*70)
# as Q_b -> rank r<b, smallest sing value ->0, |det Psi_r|=prod nonzero sig ->0, so |det Psi|^{-t}->inf
for eps in [1.0,1e-1,1e-2,1e-3]:
    Qb_deg = Ub@np.diag([sig[0], eps])@VbT[:b,:]   # drive 2nd sing value ->0
    s2=np.linalg.svd(Qb_deg,compute_uv=False)
    detPsi = np.prod(s2[s2>1e-14])
    print(f"  2nd sing val eps={eps:.0e}: |det Psi|={detPsi:.4f}  |det Psi|^(-t)={detPsi**(-t):.2f}  (blows up => needs A_r repair)")
