import sympy as sp

def test_cancel(M0, M1, r, label, force_factor=False):
    """
    A0 : M0 x M1 free matrix (the chart's A0u).
    P1 = A0[:, :r], P2 = A0[:, r:]  (r + s = M1).
    Lam0 = (P1^T P1)^{-1} P1^T P2.
    Question: does P1 * Lam0 == P2 ?  (off the Gram pole det(P1^T P1) != 0)
    force_factor: if True, set the bottom s columns to a linear combo of the top r columns
                  (col(P2) subset col(P1)) -- the achiever/front-bottleneck structural fact.
    """
    s = M1 - r
    # free symbolic A0
    A = sp.Matrix(M0, M1, lambda i,j: sp.Symbol(f'a_{i}_{j}'))
    if force_factor:
        # impose col(P2) subset col(P1): each of the s residual columns = P1 * (random rational coeff vector)
        Kcoef = sp.Matrix(r, s, lambda i,j: sp.Rational((i+1)*(j+2)+1, (i+j+3)))
        P1 = A[:, :r]
        P2forced = P1 * Kcoef
        for j in range(s):
            for i in range(M0):
                A[i, r+j] = P2forced[i, j]
    P1 = A[:, :r]
    P2 = A[:, r:]
    G = (P1.T * P1)
    detG = sp.simplify(G.det())
    if detG == 0:
        return label, "Gram singular symbolically", None
    Lam0 = G.inv() * P1.T * P2
    diff = sp.simplify(P1 * Lam0 - P2)
    holds = diff.is_zero_matrix
    return label, f"detG nonzero (deg poly), P1*Lam0==P2 ? {holds}", holds

# (2,3,1): M0=2,M1=3. front-bottleneck r=min(M0,M1)=2 => SQUARE (r=M0). s=1.
print(test_cancel(2,3,2, "(2,3,1) chart r=2=M0 SQUARE, free A0"))
# a TALL P1 free case: M0=3, M1=3, r=2 (r<M0). Generic free A0 -> should FAIL.
print(test_cancel(3,3,2, "M0=3 r=2<M0 TALL, free A0 (generic)"))
# same TALL but FORCE the front-bottleneck factoring col(P2) subset col(P1):
print(test_cancel(3,3,2, "M0=3 r=2<M0 TALL, FORCED col(P2) in col(P1)", force_factor=True))
# wide P1 (r > M0): M0=2, M1=4, r=3 -> P1 is 2x3 (full row rank generically) col(P1)=R^2 superset col(P2)
print(test_cancel(2,4,3, "M0=2 r=3>M0 WIDE P1, free A0"))
