#!/usr/bin/env python3
"""Why is Q2 (and the Schur complement) a COORDINATE change on the source, but Q1 forced to
remain an IDEAL COFACTOR?  The principled test: is the induced map on the source coords a
diffeomorphism (invertible, det!=0) or a projection (collapses a coord, det=0)?
(3,3,4), chart c11=1.  sympy exact."""
import sympy as sp
ok = True
c12a,c12b,c21a,c21b = sp.symbols('c12a c12b c21a c21b')
m = sp.symbols('m11 m12 m21 m22'); C22 = sp.Matrix(2,2,m)
C12 = sp.Matrix([[c12a,c12b]]); C21 = sp.Matrix([[c21a],[c21b]])
C1 = sp.Matrix([[1,c12a,c12b],[c21a,m[0],m[1]],[c21b,m[2],m[3]]])
Q1 = sp.eye(3); Q1[1,0]=-c21a; Q1[2,0]=-c21b
Q2 = sp.eye(3); Q2[0,1]=-c12a; Q2[0,2]=-c12b

oldC1 = [c12a,c12b,c21a,c21b,m[0],m[1],m[2],m[3]]

# --- candidate coordinate change A: right op Q2 + Schur  (C22 -> Delta) ---
Delta = C22 - C21*C12
newA = [c12a,c12b,c21a,c21b, Delta[0,0],Delta[0,1],Delta[1,0],Delta[1,1]]
detA = sp.simplify(sp.Matrix(newA).jacobian(oldC1).det())
print("A: (Schur C22->Delta, keep C12,C21) det =", detA, "-> INVERTIBLE shear (uses C21,C12 to shear C22)")
ok &= (detA == 1)

# --- candidate coordinate change B: LEFT op Q1 on C1 (C1 -> Q1 C1) ---
Q1C1 = Q1*C1
# the induced map on the 8 non-pivot coords of C1: what does Q1 C1 produce?
# row0 stays (1,c12a,c12b); rows1,2 = (col0, C22) - C21*(1,C12)
newB_entries = [Q1C1[0,1],Q1C1[0,2], Q1C1[1,0],Q1C1[2,0], Q1C1[1,1],Q1C1[1,2],Q1C1[2,1],Q1C1[2,2]]
detB = sp.simplify(sp.Matrix(newB_entries).jacobian(oldC1).det())
print("B: (LEFT op C1->Q1 C1)              det =", detB,
      "-> NON-invertible: col0 rows12 =", [sp.simplify(Q1C1[1,0]),sp.simplify(Q1C1[2,0])],
      "(c21 cleared to 0) -> projection, NOT a coord change")
ok &= (detB == 0)

print()
print("CONCLUSION: Q2 / Schur use KEPT coords (C12,C21) to shear OTHER coords (C22,C2-row0)")
print("  -> invertible (det 1) -> COORDINATE CHANGES folded into g, Jacobian EXACTLY 1.")
print("  Q1 uses C21 to clear C21 itself -> det 0 projection -> CANNOT be a coord change")
print("  -> it survives as the RegionRepresents ideal cofactor (row recombination of the")
print("     output family). This is forced, not a choice; and it is why the loss is not")
print("     Frobenius-preserved (Q1 non-orthogonal left factor stays in the product).")
print("\nROLES PIN:", "PASS" if ok else "FAIL")
import sys; sys.exit(0 if ok else 1)
