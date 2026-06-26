import sympy as sp

# ===========================================================================================
# GENERAL m x k reduced node. Â: m x k, Â[0,0]=1 HARD (post-blow-up pivot). A2: k x n.
# flatCore = F = ‖Â·A2‖²_F  (the actual dlnLoss M 0 at this node).
# Regular gens: E_j := (Â·A2)[0,j],  j=0..n-1   (the pivot ROW of the product).
# Schur complement: write Â = [[1, a],[b, D]],  a = Â[0,1:] (1 x (k-1)), b = Â[1:,0] ((m-1) x 1),
#   D = Â[1:,1:] ((m-1) x (k-1)).  S := D - b·a   ((m-1) x (k-1)).
# A2red := A2[1:,:]  ((k-1) x n)  — the reduced second factor (rows 1..k-1 of A2).
# Φ := Σ_j E_j² + ‖S·A2red‖²_F.
#
# CLAIM (the load-bearing Schur identity, read as ideal-membership):
#   the LOWER rows of Â·A2 satisfy   (Â·A2)[1:,:]  =  b · E_row  +  S · A2red
#   where E_row = (Â·A2)[0,:] = the row vector (E_0,...,E_{n-1}).
#   ⟹  F - Φ = ‖(Â·A2)[1:,:]‖² - ‖S·A2red‖²  ∈ ideal(E_0,...,E_{n-1})   (vanishes on {E=0}).
#
# Prove SYMBOLICALLY in block form, then VERIFY on concrete shapes incl. non-square.
# ===========================================================================================

def run(m, k, n, label):
    # build Â with hard pivot
    A = sp.Matrix(m, k, lambda i,j: sp.Integer(1) if (i,j)==(0,0) else sp.Symbol(f'a_{i}_{j}'))
    B = sp.Matrix(k, n, lambda i,j: sp.Symbol(f'b_{i}_{j}'))
    M = sp.expand(A*B)                                  # the product Â·A2  (m x n)
    Erow = M[0:1, :]                                    # E_row = pivot row (1 x n)
    E = [M[0,j] for j in range(n)]
    a = A[0:1, 1:]                                      # 1 x (k-1)
    b = A[1:, 0:1]                                      # (m-1) x 1
    D = A[1:, 1:]                                       # (m-1) x (k-1)
    S = sp.expand(D - b*a)                              # Schur complement (m-1)x(k-1)
    A2red = B[1:, :]                                    # (k-1) x n
    lower = M[1:, :]                                    # (Â·A2)[1:,:]  (m-1) x n

    # (1) THE SCHUR IDENTITY:  lower == b·E_row + S·A2red
    rhs = sp.expand(b*Erow + S*A2red)
    id_diff = sp.expand(lower - rhs)
    ok_identity = id_diff == sp.zeros(m-1, n)

    # (2) F - Φ vanishes on {E=0}  (ideal membership).  E_j = M[0,j] = b_{0,j} + Σ_{i>=1} a_{0,i} b_{i,j}.
    #     Solve E=0 for the pivot-row vars b_{0,j}:  b_{0,j} = -Σ_{i>=1} a_{0,i} b_{i,j}.
    def fro2(X): return sp.expand(sum(X[i,j]**2 for i in range(X.rows) for j in range(X.cols)))
    F   = fro2(M)
    Phi = sp.expand(sum(e**2 for e in E) + fro2(sp.expand(S*A2red)))
    subE = { B[0,j]: -sum(A[0,i]*B[i,j] for i in range(1,k)) for j in range(n) }
    FmP_onE0 = sp.simplify((F - Phi).subs(subE))
    ok_ideal = FmP_onE0 == 0

    # (3) explicit: F - Φ = ‖lower‖² - ‖S·A2red‖²  and using (1), lower = b·E + S·A2red, so
    #     ‖lower‖² - ‖S·A2red‖² = Σ (b·E + S·A2red)² - Σ(S·A2red)²
    #       = Σ [ (b·E)² + 2 (b·E)·(S·A2red) ]   -- every term carries a factor E_j ⟹ ∈ ideal(E). Verify:
    cross = sp.expand(fro2(lower) - fro2(sp.expand(S*A2red)) - (F - Phi))  # should be 0 (def of F-Φ via rows)
    # NOTE F = ‖row0‖² + ‖lower‖² = ΣE² + ‖lower‖²; Φ = ΣE² + ‖S·A2red‖²; so F-Φ = ‖lower‖²-‖S·A2red‖² exactly.
    ok_rowsplit = sp.expand(F - (sum(e**2 for e in E) + fro2(lower))) == 0

    print(f"[{label}]  (m,k,n)=({m},{k},{n})")
    print(f"   (1) Schur identity  lower = b·E_row + S·A2red : {'HOLDS' if ok_identity else 'FAIL '+str(id_diff)}")
    print(f"   (2) (F-Φ)|{{E=0}} = 0  (ideal-membership)      : {'HOLDS' if ok_ideal else 'FAIL '+str(FmP_onE0)}")
    print(f"   (3a) F = ΣE² + ‖lower‖²  (row split)           : {'HOLDS' if ok_rowsplit else 'FAIL'}")
    print(f"   (3b) F-Φ = ‖lower‖²-‖S·A2red‖² consistency     : {'HOLDS' if cross==0 else 'FAIL'}")
    return ok_identity and ok_ideal and ok_rowsplit and (cross==0)

print("=== GENERAL Schur ideal-membership certification (multiple shapes) ===\n")
results = []
for (m,k,n,lbl) in [(3,3,3,"square (3,3,3) — the #129 node"),
                    (4,3,2,"non-square Â tall (4,3,2)"),
                    (2,4,3,"non-square Â wide (2,4,3)"),
                    (3,2,2,"k=2 minimal Schur (3,2,2)"),
                    (5,4,3,"larger (5,4,3)"),
                    (2,2,1,"n=1 single-col target (2,2,1)")]:
    results.append(run(m,k,n,lbl)); print()
print("ALL SHAPES PASS:", all(results))
