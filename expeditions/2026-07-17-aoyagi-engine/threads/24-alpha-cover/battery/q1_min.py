#!/usr/bin/env python3
# Q1: is carrying the FULL residual block D_J minimal vs PIVOT-CROSS-ONLY (row+col of step J)?
# KILL = a reachable D_J where pivot-cross-only CANNOT produce D_{J+1} for step J+1's hypothesis.
# D_{J+1} = Schur complement of the pivot = interior - (pivot col)(pivot row)  (corner normalized to 1).
import sympy as sp

def schur_next(D):
    """D_{J+1} = interior - col*row (pivot corner D[0,0] normalized to 1)."""
    m, n = D.shape
    p = D[0,0]
    col = sp.Matrix([D[i,0] for i in range(1,m)])      # pivot column (below corner)
    row = sp.Matrix([[D[0,j] for j in range(1,n)]])    # pivot row (right of corner)
    interior = D[1:m, 1:n]
    return sp.simplify(interior - (col*row)/p)

# A reachable 3x3 residual D_0 (two spine steps). Corner normalized to 1.
a01,a02,a10,a20 = sp.symbols('a01 a02 a10 a20', real=True)     # pivot cross of step 0
w11,w12,w21,w22 = sp.symbols('w11 w12 w21 w22', real=True)     # interior 2x2
D0 = sp.Matrix([[1, a01, a02],[a10, w11, w12],[a20, w21, w22]])
D1 = schur_next(D0)
print("="*80); print("Q1 minimality: can pivot-cross-only reconstruct D_1?"); print("="*80)
print("D_1 (Schur complement, 2x2) =")
sp.pprint(D1)
print("\nStep 1 hypothesis reads D_1's pivot corner D_1[0,0] =", sp.factor(D1[0,0]))
print("  -> depends on the INTERIOR entry w11 (= D_0[1,1]), which pivot-cross {a01,a02,a10,a20} DISCARDS.")

# Witness: two D_0 with IDENTICAL pivot cross but different interior -> different D_1
sub_common = {a01:sp.Rational(1,2), a02:0, a10:sp.Rational(1,3), a20:0, w12:0,w21:0,w22:1}
D0_A = D0.subs({**sub_common, w11:1})
D0_B = D0.subs({**sub_common, w11:2})
D1_A = schur_next(D0_A); D1_B = schur_next(D0_B)
cross_A = (D0_A[0,1],D0_A[0,2],D0_A[1,0],D0_A[2,0])
cross_B = (D0_B[0,1],D0_B[0,2],D0_B[1,0],D0_B[2,0])
print("\nWITNESS (same pivot cross, different interior):")
print(f"  cross_A == cross_B : {cross_A == cross_B}   (cross = {cross_A})")
print(f"  D_1[0,0]  A = {sp.simplify(D1_A[0,0])} ,  B = {sp.simplify(D1_B[0,0])}   differ? {sp.simplify(D1_A[0,0]-D1_B[0,0])!=0}")
print("\nVERDICT Q1:", "KILL confirmed — pivot-cross-only CANNOT produce D_1 (the Schur complement needs the interior). "
      "FULL block (option 2 / option-C exposure) is minimal; option 3 (pivot-cross-only) FAILS.")
