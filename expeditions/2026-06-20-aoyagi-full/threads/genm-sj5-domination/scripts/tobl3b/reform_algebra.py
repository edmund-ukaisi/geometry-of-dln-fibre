import numpy as np, sympy as sp

print("="*70)
print("(1) Gram-Schmidt determinant product  det(Q Qᵀ) = ∏_i ‖q_i^⊥‖²")
print("="*70)
# symbolic b=2, n=3
def gram_det(Q):
    return sp.simplify((Q*Q.T).det())
def gs_perp_normsq(Q):
    # rows q_i; q_i^⊥ = q_i - proj onto span(q_1..q_{i-1}); return list ‖q_i^⊥‖²
    b = Q.rows
    perps=[]; basis=[]
    for i in range(b):
        qi = Q.row(i).T  # column
        v = qi
        for u in basis:
            v = v - (u.dot(qi)/u.dot(u))*u
        perps.append(sp.simplify(v.dot(v)))
        basis.append(v)
    return perps
for b,n in [(2,3),(3,4)]:
    Q = sp.Matrix(b,n, lambda i,j: sp.symbols(f'q{i}{j}'))
    lhs = gram_det(Q)
    prod = sp.simplify(sp.prod(gs_perp_normsq(Q)))
    print(f" b={b},n={n}: det(QQᵀ) - ∏‖q_i^⊥‖²  simplifies to  {sp.simplify(lhs-prod)}")

print()
print("="*70)
print("(2) innermost single-row integral is a frobSq(A_b · (Z·Π)) integrand")
print("="*70)
# q_b^⊥ = A_b·Z projected orth to V_{b-1}=span(q_1..q_{b-1}).  With Π = I - proj_{V},
# q_b^⊥ = (A_b Z) Π  (row), so ‖q_b^⊥‖² = ‖A_b (ZΠ)‖²_F = frobSq(A_b·(ZΠ)).
# numeric check
rng=np.random.default_rng(0)
for trial in range(3):
    M2,n,b=4,5,3
    Z=rng.standard_normal((M2,n)); A=rng.standard_normal((b,M2))
    Q=A@Z
    V=Q[:b-1]                      # previous rows' images (span V_{b-1})
    # projector onto V^perp in R^n
    P_V = V.T@np.linalg.pinv(V@V.T)@V
    Pi = np.eye(n)-P_V
    qb=Q[b-1]
    qb_perp = qb - qb@P_V
    lhs = qb_perp@qb_perp
    rhs = np.linalg.norm(A[b-1]@(Z@Pi))**2   # frobSq(A_b·(ZΠ))
    print(f" trial {trial}: ‖q_b^⊥‖²={lhs:.6f}   frobSq(A_b·ZΠ)={rhs:.6f}   diff={abs(lhs-rhs):.2e}")

print()
print("="*70)
print("(3) entanglement: after integrating A_b (SPEC → sigMin(ZΠ)^{-α'}), the")
print("    residual factor depends on the OUTER rows through Π=Π(A_1..A_{b-1})")
print("="*70)
# show sigMin(ZΠ) varies with the outer rows A_1..A_{b-1}
M2,n,b=4,6,3
Z=rng.standard_normal((M2,n))
for t in range(3):
    A_outer=rng.standard_normal((b-1,M2))
    V=A_outer@Z
    P_V=V.T@np.linalg.pinv(V@V.T)@V; Pi=np.eye(n)-P_V
    ZPi=Z@Pi
    s=np.linalg.svd(ZPi,compute_uv=False)
    print(f" outer-row draw {t}: smallest nonzero sing val of ZΠ (the SPEC tail) = {s[s>1e-9].min():.5f}"
          f"  (varies with outer rows ⇒ sigMin^{{-α'}} entangles the outer integral)")
