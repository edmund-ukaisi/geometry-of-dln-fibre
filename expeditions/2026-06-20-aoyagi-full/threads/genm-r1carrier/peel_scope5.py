"""
C10 : the VERDICT-FLIPPING probe -- deepest-layer-first ordering.
      Claim to test: if A2 is resolved to a monomial normal form A2 = U . D . V (U,V units,
      D 3x4 monomial-diagonal) BEFORE the corank block is freed, does Qb = A1b . A2 become
      monomial x unit, so det(Qb Qb^T) principalises torically (=> BOUNDED, verdict flips)?

  Structural reduction (exact): Qb = A1b.U.D.V = A'.D.V, A' = A1b.U (2x3, generic since U unit).
  With V unit (V V^T pos-def), det(Qb Qb^T) ~ det(A'.D.(A'.D)^T) = sum_{k<l} (d_k d_l)^2 * p_kl(A')^2,
  p_kl(A') = 2x2 minors of the 2x3 block A'.  So the residual determinantal object is I_2(A'), the
  minor ideal of a 2x3 FREE block.  Test: does I_2(A') have a dense-torus zero (=> still non-coord)?

C11 : consistency of the free-tail BOUNDED claim -- it is bounded via the ALTERNATIVE banked
      SchurCore/rrp route (a two-matrix core argument), NOT via toric principalisation of det.  Confirm
      the 2x3 free minor ideal is itself determinantal (so the free case is NOT toric either; its
      boundedness comes from the SchurCore escape available only when Qp, Qb are INDEPENDENT).
"""
import sympy as sp
from itertools import combinations

print("C10 : does deepest-layer-first (resolve A2 to U.D.V) make Qb monomial x unit?")
# A' = A1b . U  is a generic 2x3 block; residual det(QbQb^T) ~ sum (d_k d_l)^2 p_kl(A')^2.
Ap = sp.Matrix(2,3, sp.symbols('p0:6', real=True))     # A' = A1b.U (2x3, generic)
colpairs3 = list(combinations(range(3),2))
p = {kl: Ap[0,kl[0]]*Ap[1,kl[1]] - Ap[0,kl[1]]*Ap[1,kl[0]] for kl in colpairs3}
print("   residual minors p_kl(A') of the 2x3 block:", [sp.expand(p[kl]) for kl in colpairs3])
# dense-torus zero of I_2(A')?  A' = [[1,1,1],[1,1,1]] : all entries nonzero, rank 1.
Anum = sp.Matrix([[1,1,1],[1,1,1]])
pnum = [Anum[0,kl[0]]*Anum[1,kl[1]] - Anum[0,kl[1]]*Anum[1,kl[0]] for kl in colpairs3]
print("   A'=[[1,1,1],[1,1,1]] all-nonzero, minors:", pnum, "-> rank", Anum.rank(),
      " => DENSE-TORUS zero of I_2(A').")
print("   => even AFTER resolving A2 first, the residual carries I_2 of the 2x3 free block A', which")
print("      STILL has a dense-torus rank-drop -> non-coordinate center STILL forced.  VERDICT HOLDS:")
print("      deepest-layer-first does NOT rescue boundedness.  RESEARCH-GRADE confirmed.")

print()
print("C11 : is the free 2x4 / 2x3 corank-2 case toric?  (it is NOT; it is bounded via SchurCore)")
Yb = sp.Matrix(2,4, sp.symbols('y0:8', real=True))
colpairs4 = list(combinations(range(4),2))
# dense-torus zero of I_2 of a free 2x4:
Ynum = sp.Matrix([[1,1,1,1],[1,1,1,1]])
mins = [Ynum[0,ij[0]]*Ynum[1,ij[1]]-Ynum[0,ij[1]]*Ynum[1,ij[0]] for ij in colpairs4]
print("   free 2x4 Y=[[1,1,1,1],[1,1,1,1]] all-nonzero, minors:", mins, "rank", Ynum.rank(),
      "-> DENSE-TORUS zero.")
print("   => the FREE corank-2 Gram det is ALSO determinantal (non-toric).  So the free case is NOT")
print("      bounded because det principalises torically -- it is bounded because at depth<=3 the tail")
print("      is a SINGLE free matrix, Qp and Qb are INDEPENDENT row-blocks, and the banked SchurCore/")
print("      routeMBoxThresholdFinite_rrp closes it by a two-matrix-core argument (NO det principalisation).")
print("   => the product case (depth>=4) has NO such escape: Qp, Qb SHARE the deeper product Z, so the")
print("      SchurCore decoupling is unavailable and the product-minor principalisation is unavoidable.")
print()
print("REFINED SCOPE: 'free single-matrix tail -> BOUNDED' holds via the SchurCore ESCAPE (banked),")
print("not via toric principalisation.  The research-grade line is: corank>=2 AND SHARED deeper product")
print("(Qp, Qb both factor through the same Z), i.e. genuine product tail, depth>=4.")
