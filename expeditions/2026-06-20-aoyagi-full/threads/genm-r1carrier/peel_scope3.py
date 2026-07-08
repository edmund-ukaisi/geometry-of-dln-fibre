"""
C7 : verify Codex's DENSE-TORUS rank-drop witness (Q4) and the saturation discriminator.
     If {rank(A1b*A2)<=1} has a point with ALL entries nonzero, that point is invisible to any
     coordinate/toric blow-up center => coordinate blow-ups cannot principalise I_2(A1b*A2)
     => a NON-coordinate (determinantal/Plucker) center is forced (RESEARCH-GRADE).
"""
import sympy as sp
from itertools import combinations

# Codex's explicit witness
B = sp.Matrix([[1,1,1],[1,2,3]])                    # 2x3, all entries nonzero
C = sp.Matrix([[3,4,5,5],[-4,-6,-6,-8],[2,3,3,4]])  # 3x4, all entries nonzero
BC = B*C
print("Codex witness B*C =")
sp.pprint(BC)
print("all entries of B nonzero:", all(e != 0 for e in B), " all entries of C nonzero:", all(e != 0 for e in C))
print("all entries of B*C nonzero:", all(e != 0 for e in BC))
print("rank(B*C) =", BC.rank(), " (=1 => on {rank<=1}, i.e. det(QbQb^T)=0)")
colpairs4 = list(combinations(range(4),2))
mins = [BC[0,ij[0]]*BC[1,ij[1]]-BC[0,ij[1]]*BC[1,ij[0]] for ij in colpairs4]
print("all 2x2 minors of B*C vanish:", all(m==0 for m in mins), " minors =", mins)
print()
print(">>> A rank-drop point in the DENSE TORUS (all coords nonzero) confirms V(I_2(Qb)) is NOT")
print("    contained in any coordinate-subspace arrangement.  Coordinate/toric single-radial")
print("    blow-ups (centers = coordinate strata) CANNOT separate/monomialise it.  A determinantal")
print("    (non-coordinate) center is forced.  This is the toric-insufficiency discriminator.")

print()
print("C8 : saturation check on the SYMBOLIC product-minor ideal (Codex Q4).")
print("     (I_2(A1b*A2) : (prod of all entries)^inf) != (1)  <=>  torus rank-drop points exist.")
a = sp.symbols('a0:6'); A1b = sp.Matrix(2,3,a)
b = sp.symbols('b0:12'); A2 = sp.Matrix(3,4,b)
Qb = sp.expand(A1b*A2)
minorQb = [sp.expand(Qb[0,ij[0]]*Qb[1,ij[1]]-Qb[0,ij[1]]*Qb[1,ij[0]]) for ij in colpairs4]
# We do not need full saturation (heavy); the explicit torus witness already proves non-emptiness of
# the saturated locus.  Record the structural fact:
print("    The explicit torus point above is a zero of ALL", len(minorQb), "minor generators with no")
print("    coordinate vanishing, so the saturation is a proper non-unit ideal (>=1 torus component).")
print("    => coordinate blow-ups insufficient; CONFIRMED RESEARCH-GRADE.")
