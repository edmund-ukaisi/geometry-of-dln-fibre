import sympy as sp
import numpy as np

print("="*72)
print("STEP 1: exact Jacobian of Y -> Q = Y*A at fixed A, SQUARE case m=q")
print("="*72)
# Y: b x m,  A: m x q,  Q = Y A : b x q.  Square balanced case m=q.
# Map on b*m coords -> b*q coords. Verify Jacobian determinant = det(A)^b.
for (b,m,q) in [(1,1,1),(1,2,2),(2,2,2),(2,3,3),(3,2,2)]:
    if m!=q: continue
    Y = sp.Matrix(b, m, lambda i,j: sp.Symbol(f'y_{i}_{j}'))
    A = sp.Matrix(m, q, lambda i,j: sp.Symbol(f'a_{i}_{j}'))
    Q = Y*A
    yvars = list(Y)
    qexpr = list(Q)
    Jmat = sp.Matrix([[sp.diff(qe, yv) for yv in yvars] for qe in qexpr])
    Jdet = sp.simplify(Jmat.det())
    detA_b = sp.simplify(A.det()**b)
    print(f"(b,m,q)=({b},{m},{q}): dQ/dY det = detA^b ?  residual =",
          sp.simplify(Jdet - detA_b))
print()
print("=> dQ = |det A|^b dY,  so  dY = |det A|^{-b} dQ.")
print("   J(A) = |det A|^{-b} = det(A A^T)^{-b/2}  (square case). CONFIRMED.")

print()
print("="*72)
print("STEP 2: general pseudo-det Jacobian via SVD (numeric), regimes m vs q")
print("="*72)
# For A: m x q rank r, the row-map v|->vA pushforward density factor is
#  prod of nonzero singular values.  Over b rows: J ~ (prod sigma_i)^{-b}.
# Check: for m>=q full rank, prod sigma = sqrt(det(A^T A)) (q x q).
#        for m<=q full rank, prod sigma = sqrt(det(A A^T)) (m x m).
rng = np.random.default_rng(0)
for (m,q) in [(2,2),(3,2),(2,3),(4,2),(2,4)]:
    A = rng.standard_normal((m,q))
    sv = np.linalg.svd(A, compute_uv=False)
    prod_sv = np.prod(sv[sv>1e-12])
    r = min(m,q)
    if m>=q:
        alt = np.sqrt(np.linalg.det(A.T@A))
        name="sqrt det(A^T A) [q x q]"
    else:
        alt = np.sqrt(np.linalg.det(A@A.T))
        name=f"sqrt det(A A^T) [m x m]"
    print(f"(m,q)=({m},{q}) rank={r}: prod nonzero sv={prod_sv:.5f}  {name}={alt:.5f}  match={np.isclose(prod_sv,alt)}")
print()
print("=> generic rank r=min(m,q). J(A) = pseudo-det Gram ^(-b/2):")
print("   m>=q: J = det(A^T A)^{-b/2}  (q x q Gram of COLUMNS)")
print("   m<=q: J = det(A A^T)^{-b/2}  (m x m Gram of ROWS)")
print("   BOTH are determinantal corank-Gram weights on the deeper tail A.")
