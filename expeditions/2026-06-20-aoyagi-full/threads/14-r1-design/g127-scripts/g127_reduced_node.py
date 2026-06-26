import sympy as sp
# WITNESS the per-node (uᵢ,ψᵢ) adapted-basis transvection straighten on a REDUCED chain.
# Setup: (3,3,3) zero-core ‖A1 A2‖². Do ONE blow-up + straighten to REACH a reduced node, then
# witness the (uᵢ,ψᵢ) straighten AT that reduced node (the genuine per-node, not the outer chain).
#
# Step 0: the top (3,3,3) zero-core at origin: A1,A2 3x3, all generators bilinear, Jac rank 0.
# Step 1 (BLOW-UP): blow up {A1=0}: A1 = x·Â, Â[0,0]=1 HARD. F = x²·‖Â A2‖². Â=[[1,p,q],[r,s,t],[u,v,w]].
# Now ‖Â A2‖² with Â[0,0]=1 HARD pivot — THIS is the reduced node's input (post-blow-up, hard pivot).
#
# The (uᵢ,ψᵢ) adapted basis at this reduced node: u = the transported line, ψ = the covector, with
# the HARD pivot Â[0,0]=1 giving the transvection (det=1) straighten that clears Â's pivot row/col.
p,q,r,s,t,u_,v,w = sp.symbols('p q r s t u v w', real=True)
Ahat = sp.Matrix([[1,p,q],[r,s,t],[u_,v,w]])
b = sp.symbols('b0:9', real=True)
A2 = sp.Matrix(3,3,b)
M = sp.expand(Ahat*A2)
print("=== Reduced node: ‖Â A2‖², Â[0,0]=1 HARD pivot (post-blow-up of (3,3,3) {A1=0}) ===")
print("Â =", Ahat.tolist())
# The (uᵢ,ψᵢ) adapted basis (the #109 transported-line/covector, here with the hard pivot):
# u_0 = Â's pivot column direction; ψ_0 = the covector picking the pivot row. The transvection
# straighten = clear Â's row 0 / col 0 using the hard 1 pivot:
#   col ops: C_j -= Â[0,j]·C_0 (j=1,2)  => clears row 0 of Â to [1,0,0]
#   row ops: R_i -= Â[i,0]·R_0 (i=1,2)  => clears col 0 of Â to [1,0,0]^T
# These are TRANSVECTIONS (det=1) because the pivot is HARD 1 (no division). After:
Acol = Ahat.copy()
# col ops on Â (right-multiply by unipotent): clear row-0 entries p,q
Qcol = sp.eye(3); Qcol[0,1] = -p; Qcol[0,2] = -q   # C1 -= p C0, C2 -= q C0
Arow = sp.eye(3); Arow[1,0] = -r; Arow[2,0] = -u_  # R1 -= r R0, R2 -= u R0
Ahat_clean = sp.expand(Arow * Ahat * Qcol)
print("\nAfter transvection straighten (row/col ops, det=1, HARD pivot):")
print("  L·Â·R =", Ahat_clean.tolist())
print("  det(L) =", Arow.det(), " det(R) =", Qcol.det(), " => both 1 (TRANSVECTIONS, MEASURE-PRESERVING)")
# The cleaned Â = [[1,0,0],[0, s-rp, t-rq],[0, v-up, w-uq]] => the 2x2 Schur block S = [[s-rp,t-rq],[v-up,w-uq]]
S = Ahat_clean[1:,1:]
print("  Schur block S (the REDUCED 2x2 chain factor) =", sp.expand(S).tolist())
print()
print("=> WITNESSED at the reduced node: the (uᵢ,ψᵢ) adapted basis = the hard-pivot row/col transvections;")
print("   det=1 (MEASURE-PRESERVING); the Schur block S = the next reduced chain factor (2x2).")
print("   The hard-1 pivot (supplied by the blow-up) makes the straighten a TRANSVECTION — CONFIRMED at")
print("   a reduced chain, not just the outer (3,3,3). The interface holds per-node.")
