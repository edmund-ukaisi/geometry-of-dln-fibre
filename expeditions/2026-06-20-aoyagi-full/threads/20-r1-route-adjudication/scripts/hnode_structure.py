"""
Q1 (continued) — Does the per-node squeeze form `hnode` capture the actual peel?

The hnode form (GeneralR1Recursion.lean:620-623), reading w.1 = Erow (nReg regular
coords = pivot-row product), is

    flatCore = ∑_j Erow_j²  +  ∑_{i,j} (bcol_i · Erow_j + SΓ_{i,j})²    ... (HNODE)
    G²       = ∑_{i,j} SΓ_{i,j}²

This is EXACTLY the schur_row_decomp output (GeneralR1Recursion.lean:472):
   lower rows of  Â·A2  =  b · E_row  +  S · A2red
i.e. (lower)_{i,j} = bcol_i · Erow_j + (S·A2red)_{i,j}, with SΓ = S·A2red.

The KEY structural assumption baked into hnode: the cross term is the
RANK-1 outer product  bcol ⊗ Erow.  This is the HARD-1-PIVOT Schur step:
ONE pivot cleared (1×1 block A₁=1), b = Â[1:,0] a COLUMN vector, Erow a ROW vector.

QUESTION: at a corank-≥2 peel, is the cross term still rank-1 bcol⊗Erow?
At (3,3,4) t=(1,0): we clear ONE pivot of the 3×3 layer-1; residual block Δ is 2×2.
After block-elim the lower rows are weighted by Δ (a 2×2), and the bottom structure is
   F = ‖T·C‖² + ‖Δ·S·C‖²     (verify-r1-light §, c334_peel.py)
We test: is ‖Δ·S·C‖² expressible as ∑(bcol_i·Erow_j + SΓ_{i,j})² with bcol a single
column and Erow the SAME pivot-row used for the regular block?  If not, hnode cannot
hold at this node.
"""
import sympy as sp

print("=== Test A: hard-1-pivot Schur => cross term IS rank-1 (hnode faithful) ===")
# One pivot cleared: A = [[1, β],[b_col, D]] (β a 1×n row, b_col an m×1 col, D m×n).
# schur_row_decomp: lower rows of [[1,β],[b,D]] · [[Erow],[Γ]] ... actually the product
# Â·A2 where Â has hard pivot. We reproduce the schur_row_decomp identity exactly:
#   b*β_blk + D*Γ = b*(1*β_blk + a*Γ) + (D - b*a)*Γ
# Here pivot-row product Erow = 1*β + a*Γ, and lower = b·Erow + S·Γ, S = D - b·a.
m, n, k = 2, 2, 2
a = sp.Matrix(1, k, lambda i,j: sp.Symbol(f'a_{j}'))      # 1×k  (pivot row's a-part)
bcol = sp.Matrix(m, 1, lambda i,j: sp.Symbol(f'b_{i}'))    # m×1  pivot column
D = sp.Matrix(m, k, lambda i,j: sp.Symbol(f'D_{i}{j}'))
beta = sp.Matrix(1, n, lambda i,j: sp.Symbol(f'be_{j}'))   # 1×n
Gam = sp.Matrix(k, n, lambda i,j: sp.Symbol(f'G_{i}{j}'))  # k×n
Erow = (sp.ones(1,1)*beta + a*Gam)        # 1×n   pivot-row product (= w.1, the regular coords)
S = D - bcol*a                            # m×k   Schur complement
lower = bcol*beta + D*Gam                 # m×n   the actual lower rows
SGam = S*Gam                              # m×n
# hnode claims lower_{i,j} = bcol_i·Erow_j + SGam_{i,j}
claim = sp.zeros(m,n)
for i in range(m):
    for j in range(n):
        claim[i,j] = bcol[i,0]*Erow[0,j] + SGam[i,j]
diff = sp.simplify(lower - claim)
print("  lower - (bcol⊗Erow + S·Γ) = 0 ? :", diff == sp.zeros(m,n))
print("  => with ONE pivot cleared, the cross term IS the rank-1 outer product bcol⊗Erow.")
print()

print("=== Test B: corank-2 (TWO pivots remain) => cross term is NOT rank-1 ===")
# (3,3,4) layer-1 peel at t=(1,0): clear ONE pivot, residual Δ is 2×2 (corank 2).
# The actual structure (c334_peel.py): F = ‖T·C‖² + ‖Δ·S·C‖², Δ free 2×2, S free 2×4, C free 4×?.
# The 'lower' block here is Δ·(S·C). Is (Δ·SC)_{i,j} = bcol_i · Erow_j + something,
# with bcol a SINGLE column and Erow the regular pivot-row?  Δ is 2×2 RANK 2 generically,
# so Δ·SC has rank up to 2 in its bilinear part — cannot be a single rank-1 outer product
# plus an SΓ that is the REDUCED-CHAIN loss.
Delta = sp.Matrix(2,2, lambda i,j: sp.Symbol(f'd_{i}{j}'))   # the residual 2×2 block (free)
SC = sp.Matrix(2,2, lambda i,j: sp.Symbol(f'x_{i}{j}'))      # S·C, a 2×2 (free, the deep tail)
lowerCorank2 = Delta*SC
# The bilinear cross structure: lowerCorank2 is a genuine matrix PRODUCT of two free 2×2
# matrices. The 'rank-1 bcol⊗Erow' ansatz would force the i-dependence to factor through a
# single column. Check: does lowerCorank2 factor as bcol(i)*Erow(j) + SΓ(i,j) with the SAME
# Erow across rows and SΓ = the reduced loss generators?  The reduced loss here would be ‖SC‖²
# i.e. SΓ = SC and bcol⊗Erow would have to equal (Δ - I)·SC — which is NOT rank-1 (Δ-I free 2×2).
resid = Delta*SC - SC          # (Δ - I)·SC, the "extra" beyond the reduced core SC
print("  (Δ-I)·SC  rank (generic) :", (Delta - sp.eye(2)).rank(), "x", "-> matrix product, generically rank 2")
# A rank-1 outer product bcol⊗Erow has rank ≤ 1. (Δ-I)·SC has rank up to 2.
M = sp.Matrix(2,2, lambda i,j: resid[i,j])
print("  Is (Δ-I)·SC a rank-1 outer product bcol⊗Erow?  (need 2×2 minor ≡ 0):")
minor = sp.simplify(M[0,0]*M[1,1] - M[0,1]*M[1,0])
print("    det((Δ-I)·SC) =", minor, " (≠ 0 generically => rank 2 => NOT rank-1)")
print()
print("  CONCLUSION: at corank≥2 the cross structure is a genuine 2×2 matrix product,")
print("  which is NOT the rank-1 bcol⊗Erow the hnode form hard-codes. hnode is corank-≤1.")
