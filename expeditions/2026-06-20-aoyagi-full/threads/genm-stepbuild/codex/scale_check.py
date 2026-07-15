import numpy as np
np.random.seed(0)
# dims: u pivot rows, b corank rows, n columns of deep factor, a = M0-u output rows
u, b, n, a = 3, 2, 5, 4
# random fixed data
z0 = np.random.randn(u, n)      # Q_p = z0 (u x n) [after abstracting Z into it]
Acor = np.random.randn(b, n)    # Q_b = Acor (b x n)
P = np.random.randn(u, u); 
B12 = np.random.randn(u, b)
C = np.random.randn(a, u)
q = 1.3

def frontChargeIntegrand(scale):
    # scale the deep factor: Q_p, Q_b both scale by 'scale'
    Qp = scale * z0
    Qb = scale * Acor
    G = Qb @ Qb.T                       # b x b
    detG = np.linalg.det(G)
    charge = detG ** (-a/2.0)
    Qtp = Qp                            # Q̃p = Qp + P^{-1} B Qb (pivot shear); use full form
    Qtp = Qp + np.linalg.solve(P, B12 @ Qb)
    Etop = np.linalg.norm(P @ Qtp, 'fro')**2
    Pib = Qb.T @ np.linalg.inv(Qb @ Qb.T) @ Qb   # projector onto row(Qb)
    Etr = np.linalg.norm((C @ Qtp) @ (np.eye(n) - Pib), 'fro')**2
    return charge * (Etop + Etr) ** (-q)

def comparatorIntegrand(scale):
    Qp = scale * z0
    # bare comparator: (commonDivisor^2 * ||Qp||^2)^{-q}, commonDivisor ~ O(1) scale-invariant
    return (np.linalg.norm(Qp,'fro')**2) ** (-q)

for r in [1.0, 0.1, 0.01, 0.001]:
    f = frontChargeIntegrand(r); c = comparatorIntegrand(r)
    print(f"r={r:8.4f}  front={f:12.4e}  comp={c:12.4e}  ratio={f/c:12.4e}  ratio*r^ab={f/c*r**(a*b):.4e}")
print(f"predicted front/comp ~ r^(-ab) with ab={a*b}")
