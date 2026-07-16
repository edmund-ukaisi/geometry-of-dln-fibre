import numpy as np
rng=np.random.default_rng(2)
# Verify the deep->leaf reduction is EXACT when rank Z = rho < M2.
# M2=5, n=6, rho=3 (Z = product giving rank 3). u=2,b=2,a=2 (M0=4,M1=4).
M2,n,rho,u,b,a=5,6,3,2,2,2
# Build Z (M2 x n) with rank exactly rho:
Z = rng.standard_normal((M2,rho)) @ rng.standard_normal((rho,n))
assert np.linalg.matrix_rank(Z)==rho
# rank factorization Z = Stil @ Otil, Stil: M2 x rho full col rank, Otil: rho x n with Otil Otil^T = I
U,S,Vt = np.linalg.svd(Z, full_matrices=False)   # U:M2xrho? actually U:M2 x min, S:min, Vt:min x n
U=U[:,:rho]; S=S[:rho]; Vt=Vt[:rho,:]
Stil = U*S          # M2 x rho  (=U diag(S))
Otil = Vt           # rho x n, orthonormal rows
assert np.allclose(Stil@Otil, Z)
assert np.allclose(Otil@Otil.T, np.eye(rho))

z0 = rng.standard_normal((u,M2))
Acor = rng.standard_normal((b,M2))
P = rng.standard_normal((u,u)); 
Bm = rng.standard_normal((u,b))
Cm = rng.standard_normal((a,u))

Qp = z0@Z        # u x n
Qb = Acor@Z      # b x n
# corank charge Gram
G_full = Qb@Qb.T
Qhat_b = Acor@Stil      # b x rho
G_leaf = Qhat_b@Qhat_b.T
print("det(QbQb^T) == det(Ahat Ahat^T)? ", np.allclose(np.linalg.det(G_full), np.linalg.det(G_leaf)),
      np.linalg.det(G_full), np.linalg.det(G_leaf))

# E_top = ||P Qp + B Qb||^2  vs  ||P (z0 Stil) + B (Acor Stil)||^2
Etop_full = np.sum((P@Qp + Bm@Qb)**2)
Qhat_p = z0@Stil
Etop_leaf = np.sum((P@Qhat_p + Bm@Qhat_b)**2)
print("E_top full==leaf? ", np.allclose(Etop_full,Etop_leaf), Etop_full, Etop_leaf)

# E_tr = ||C (Qp + P^{-1} B Qb)(I_n - Pi_b)||^2
Pinv=np.linalg.inv(P)
Qtp = Qp + Pinv@Bm@Qb            # u x n
Pi_b = Qb.T@np.linalg.inv(Qb@Qb.T)@Qb   # n x n
Etr_full = np.sum((Cm@Qtp@(np.eye(n)-Pi_b))**2)
# leaf: Qhat_tp = Qhat_p + P^{-1} B Qhat_b (u x rho); Pihat_b onto row(Qhat_b) in rho-space
Qhat_tp = Qhat_p + Pinv@Bm@Qhat_b
Pihat_b = Qhat_b.T@np.linalg.inv(Qhat_b@Qhat_b.T)@Qhat_b   # rho x rho
Etr_leaf = np.sum((Cm@Qhat_tp@(np.eye(rho)-Pihat_b))**2)
print("E_tr full==leaf? ", np.allclose(Etr_full,Etr_leaf), Etr_full, Etr_leaf)
