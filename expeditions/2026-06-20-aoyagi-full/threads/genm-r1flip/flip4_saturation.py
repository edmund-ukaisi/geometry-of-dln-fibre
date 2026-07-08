"""
FLIP probe 4 (deliverable B(i)) -- Groebner saturation: does I_2(A1b.A2) (the ATOM-route product-minor
ideal) genuinely FAIL to be a coordinate/monomial ideal on the torus?  If YES, the ATOM route (Gram CoV)
genuinely walls (a real determinantal locus) -- which is precisely WHY the pure coordinate route must be
used instead.  (The pure route never forms this ideal; see flip1-3.)

Test: (I_2(A1b.A2) : (prod of all entries)^inf) != (1)  <=>  V(I) has a dense-torus component.
Rabinowitsch: 1 in (I : f^inf)  <=>  1 in I + <f*w - 1> in the extended ring (Groebner basis = {1}).
"""
import sympy as sp
from itertools import combinations

# Use a SMALL faithful product 2x2 . 2x2 so the Groebner is tractable (the 2x3.3x4 has a torus witness
# already; here we CERTIFY the saturation is non-unit via a Groebner basis, exactly).
B = sp.Matrix(2,2, sp.symbols('b0:4'))
C = sp.Matrix(2,2, sp.symbols('c0:4'))
BC = sp.expand(B*C)
# maximal (2x2) minor of the 2x2 product BC (a single minor, the determinant):
minor = sp.expand(BC.det())
print("2x2.2x2:  det(B.C) =", minor, " = det(B)*det(C) (Cauchy-Binet); a genuine product of minors.")
print("  {det(B.C)=0} = {det B=0} U {det C=0}: dense-torus zeros exist e.g. B=[[1,1],[1,1]] (det 0),")
Bnum = sp.Matrix([[1,1],[1,1]]); Cnum = sp.Matrix([[1,2],[3,4]])
print("   B=[[1,1],[1,1]] (all nonzero, det 0), C generic -> det(B.C)=", (Bnum*Cnum).det(),
      " ; entries of B.C:", (Bnum*Cnum).tolist(), "(all nonzero => TORUS zero).")

print()
print("="*80)
print("Saturation of the 2x4 product minor ideal I_2(A1b.A2) by the entry product (Rabinowitsch)")
print("="*80)
a = sp.symbols('a0:6'); A1b = sp.Matrix(2,3,a)
b = sp.symbols('b0:12'); A2 = sp.Matrix(3,4,b)
Qb = sp.expand(A1b*A2)
colpairs4 = list(combinations(range(4),2))
gens = [sp.expand(Qb[0,ij[0]]*Qb[1,ij[1]]-Qb[0,ij[1]]*Qb[1,ij[0]]) for ij in colpairs4]
allvars = list(A1b.free_symbols | A2.free_symbols)
# entry product f (use a few representative entries to keep it tractable; full product is heavy):
f = sp.prod([A1b[0,j] for j in range(3)] + [A2[i,0] for i in range(3)])
w = sp.symbols('w')
# 1 in (I : f^inf) iff Groebner of I + <f*w-1> = {1}.  If NOT {1}, saturation is a PROPER ideal.
print("  (Full 18-var Groebner is heavy; the explicit dense-torus witness already certifies non-unit.)")
print("  r1carrier's exact torus witness:")
A1b_w = sp.Matrix([[1,1,1],[1,2,3]]); A2_w = sp.Matrix([[3,4,5,5],[-4,-6,-6,-8],[2,3,3,4]])
BC_w = A1b_w*A2_w
mins_w = [BC_w[0,ij[0]]*BC_w[1,ij[1]]-BC_w[0,ij[1]]*BC_w[1,ij[0]] for ij in colpairs4]
print("    A1b.A2 =", BC_w.tolist(), " all 2x2 minors:", mins_w, " all entries nonzero:",
      all(e!=0 for e in BC_w))
print("  => this torus point is a zero of ALL minor generators with NO entry vanishing, so it lies in")
print("     V(I_2) \\ V(entry-product) = V( (I_2 : (prod entries)^inf) ).  The saturation is a PROPER")
print("     (non-unit) ideal: I_2(A1b.A2) is NOT a coordinate/monomial ideal, and its rank-drop locus")
print("     is NOT contained in coordinate strata.  ATOM ROUTE (Gram CoV) genuinely WALLS. [CERTIFIED]")

# CERTIFY via a tractable proxy: the 2x2.2x2 case, full Groebner saturation, exact.
print()
print("  Tractable exact Groebner CERTIFICATE (2x2 . 2x2, single minor det(B.C)=detB*detC):")
Bv = list(B.free_symbols); Cv = list(C.free_symbols)
ff = sp.prod(Bv+Cv)   # product of all 8 entries
G = sp.groebner([minor, ff*w - 1], *(Bv+Cv+[w]), order='lex')
is_unit = (list(G.exprs) == [sp.Integer(1)])
print("    Groebner( <det(B.C), (prod entries)*w - 1> ) == {1} ? ", is_unit,
      " -> saturation is", "UNIT (no torus zero)" if is_unit else "PROPER (torus zero EXISTS)")
print("    (det B*det C vanishes on {det B=0}, a dense-torus divisor => saturation PROPER, as expected.)")
