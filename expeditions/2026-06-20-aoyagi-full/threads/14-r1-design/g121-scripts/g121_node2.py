import sympy as sp
# After node 1: R = ||Ahat A2||^2, Ahat = [[1,p],[q,r]], A2 = [[b0,b1],[b2,b3]]. Ahat[0,0]=1 unit.
# The residual singular locus (where R is still singular = where Ahat A2 has a further rank defect).
p,q,r=sp.symbols('p q r'); b=sp.symbols('b0:4')
Ahat=sp.Matrix([[1,p],[q,r]]); A2=sp.Matrix(2,2,b)
M=sp.expand(Ahat*A2)  # 2x2 product
print("Ahat A2 =")
for i in range(2):
    print("  ", [sp.expand(M[i,j]) for j in range(2)])
# The product M. With Ahat[0,0]=1 a unit, the (det-1) Lemma-2 clear: row-reduce M using row0 (pivot
# M[0,0]=b0+p b2... not a unit at origin!). Hmm. Let me reconsider: the pivot for the Schur clear is
# Ahat's structure, not M[0,0]. The (2,2,2) climb cleared via the GROUP action straightening Ahat.
#
# KEY: the det-1 Schur clears Ahat to [[1,0],[0,*]] form (using the unit pivot Ahat[0,0]=1):
# col op: subtract p*(col0) from col1 of A2-side; row op: subtract q*(row0). This is det-1 (unit pivot).
# After: Ahat ~ [[1,0],[0, r-pq]] (Schur complement r-pq in the corner). The residual rank-defect of
# the product is then governed by (r-pq) and the A2 structure -- a CLEANER coordinate.
print()
print("det-1 Schur clear of Ahat (unit pivot Ahat[0,0]=1):")
print("  row op R2 -= q R1, col op C2 -= p C1 => Ahat -> [[1,0],[0, r-pq]]. det-1 (unit pivot). ")
print("  The Schur complement = r - pq. The residual product rank-defect center becomes {r-pq=0, ...}.")
print()
print("Is {r-pq=0} a coordinate subspace? NO -- it's a hypersurface (bilinear). But after the det-1")
print("change of VARIABLE w := r - pq (a det-1 / unit-Jacobian coordinate change, since dr/dw=1), it")
print("BECOMES the coordinate {w=0}. THAT is the GL-straightening: it turns the rank-defect locus into")
print("a COORDINATE subspace, so the next blow-up (C1-style coordinate-subspace blow-up) can apply.")
print()
print("=== VERDICT: (C2) GL-straighten-THEN-blow-up. The det-1 Schur is GENUINELY NEEDED. ===")
print("Without it, the rank-defect center at node>=2 is a bilinear hypersurface {r-pq=0}, NOT a")
print("coordinate subspace -- a coordinate-subspace blow-up (the (C1) machinery) cannot be applied to it")
print("directly. The det-1 Schur straightens it to a coordinate {w=0} (unit Jacobian, no weight). So:")
print("  (C1) pure blow-up cover ALONE = INSUFFICIENT for node>=2 (center not a coordinate subspace).")
print("  (C2) GL-straighten (det-1 Schur) THEN coordinate-blow-up = the correct build. det-1 Schur NEEDED.")
print()
print("The det-1 Schur's ROLE: (i) reduces the chain (strict transform = smaller core, #109's algebra),")
print("(ii) STRAIGHTENS the rank-defect center to a coordinate subspace so the blow-up is the clean")
print("coordinate-subspace blow-up with Jacobian u^{Mval-1}. Both unit-Jacobian / det-1 / no weight.")
