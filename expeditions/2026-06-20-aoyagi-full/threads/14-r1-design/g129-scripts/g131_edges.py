import sympy as sp, numpy as np
# EDGE CASES + squeeze robustness.
def fro2(X): return sp.expand(sum(X[i,j]**2 for i in range(X.rows) for j in range(X.cols)))

# (A) m=1: Â is 1 x k (single row, [0,0]=1). Then there are NO lower rows: lower is 0 x n.
#     F = ΣE² exactly (pure regular block), Φ = ΣE² + 0 (S·A2red is 0x... empty). F=Φ. TERMINATOR.
for (m,k,n) in [(1,3,2),(1,1,4)]:
    A = sp.Matrix(m,k, lambda i,j: sp.Integer(1) if (i,j)==(0,0) else sp.Symbol(f'a_{i}_{j}'))
    B = sp.Matrix(k,n, lambda i,j: sp.Symbol(f'b_{i}_{j}'))
    Mp = sp.expand(A*B); E=[Mp[0,j] for j in range(n)]
    F = fro2(Mp); Phi = sp.expand(sum(e**2 for e in E))   # no lower block, no Schur core
    print(f"(A) m=1 (m,k,n)=({m},{k},{n}): F - ΣE² =", sp.expand(F - Phi), " (0 ⟹ pure regular block, terminator)")

# (B) k=1: Â is m x 1 ([0,0]=1 ⟹ Â=[[1],[b1],..]). A2 is 1 x n. Schur S = D - b·a but a is 1x0 (empty),
#     so S = D which is (m-1)x0 EMPTY ⟹ ‖S·A2red‖²=0, A2red is 0 x n empty. lower = b·β (rank-1).
#     F = Σ_j (Â·A2)[*,j]² ; E_j = β_j (= A2[0,j]); lower[i,j]=b_i·β_j. F-Φ = Σ b_i²β_j² = Σ E_j²·(Σb_i²)
#     ∈ ideal(E) trivially. Check:
m,k,n=3,1,2
A = sp.Matrix(m,k, lambda i,j: sp.Integer(1) if (i,j)==(0,0) else sp.Symbol(f'a_{i}_{j}'))
B = sp.Matrix(k,n, lambda i,j: sp.Symbol(f'b_{i}_{j}'))
Mp=sp.expand(A*B); E=[Mp[0,j] for j in range(n)]
F=fro2(Mp); Phi=sp.expand(sum(e**2 for e in E))  # empty Schur core
subE={B[0,j]: 0 for j in range(n)}  # E_j = B[0,j] here (k=1, no a-correction)
print(f"(B) k=1 (m,k,n)=({m},{k},{n}): (F-Φ)|{{E=0}} =", sp.simplify((F-Phi).subs(subE)), " (0 ⟹ ideal-membership; pure rank-1 outer product)")

# (C) Squeeze robustness when b (pivot column) is NOT small — the perturbation b·E_row has coeff b.
#     The squeeze c1·Φ≤F≤c2·Φ is a NEAR-0 (germ) statement; near 0 ALL of a,b,D,β,Γ → 0, so b→0 too.
#     But test: does the squeeze degrade if we fix b at O(1) while E,core→0? That is NOT the germ regime
#     (b is a coordinate, →0 at the deepest point). Confirm the germ squeeze holds with ALL vars →0:
m,k,n=3,3,3
A = sp.Matrix(m,k, lambda i,j: sp.Integer(1) if (i,j)==(0,0) else sp.Symbol(f'a_{i}_{j}'))
B = sp.Matrix(k,n, lambda i,j: sp.Symbol(f'b_{i}_{j}'))
Mp=sp.expand(A*B); E=[Mp[0,j] for j in range(n)]
a=A[0:1,1:]; bb=A[1:,0:1]; D=A[1:,1:]; S=sp.expand(D-bb*a); Gam=B[1:,:]
F=fro2(Mp); Phi=sp.expand(sum(e**2 for e in E)+fro2(sp.expand(S*Gam)))
allv=sorted(F.free_symbols, key=str); fF=sp.lambdify(allv,F,'numpy'); fP=sp.lambdify(allv,Phi,'numpy')
rng=np.random.default_rng(7); nv=len(allv)
print("(C) germ squeeze F/Φ (ALL vars→0, the deepest-point germ):")
for sc in [0.5,0.2,0.05,0.01]:
    X=rng.uniform(-sc,sc,(40000,nv)); ar=[X[:,i] for i in range(nv)]
    Fv=fF(*ar); Pv=fP(*ar); m_=np.abs(Pv)>1e-16; r=Fv[m_]/Pv[m_]
    print(f"    scale={sc}: min={r.min():.4f} max={r.max():.4f}")
print("    ⟹ F/Φ→1 as scale→0: the squeeze constants c1,c2→1 at the deepest point (germ). b→0 too, so")
print("       the linear-in-E perturbation b·E_row is higher-order; the squeeze is structural near 0.")
