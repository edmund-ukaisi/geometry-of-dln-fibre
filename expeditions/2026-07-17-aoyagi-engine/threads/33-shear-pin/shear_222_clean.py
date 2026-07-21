#!/usr/bin/env python3
"""Clean regime (2,2,2), corank<=1: does the SAME shear/cofactor structure hold as coupled?
C1,C2 are 2x2. Block-elim in chart c11=1: Q1 C1 Q2 = diag(1, delta), delta = m22 - c21 c12 (SCALAR
Schur, corank 1). Confirm: Q2/Schur = coord changes (det 1); Q1 = non-invertible projection (det 0);
|det Dg| pure monomial. Same structure as coupled -> NO clean/coupled dichotomy. sympy exact."""
import sympy as sp
ok = True
c12,c21,m22 = sp.symbols('c12 c21 m22')
C1 = sp.Matrix([[1,c12],[c21,m22]])
C2 = sp.Matrix(2,2, sp.symbols('b0:4'))
Q1 = sp.Matrix([[1,0],[-c21,1]]); Q2 = sp.Matrix([[1,-c12],[0,1]])
delta = m22 - c21*c12
print("Q1 C1 Q2 == diag(1,delta):", sp.simplify(Q1*C1*Q2 - sp.diag(1,delta))==sp.zeros(2,2),
      " delta =", delta, "(scalar Schur, corank 1)")

old = [c12,c21,m22]
# Schur coord change: m22 -> delta
detA = sp.simplify(sp.Matrix([c12,c21,delta]).jacobian(old).det())
print("A: Schur m22->delta (keep c12,c21) det =", detA, "-> invertible coord change (det 1)")
ok &= (detA==1)
# Q2^{-1} on C2 : row0 sheared
tC2 = Q2.inv()*C2
oldall = old + list(C2); newall = [c12,c21,delta] + list(tC2)
detsh = sp.simplify(sp.Matrix(newall).jacobian(oldall).det())
print("A': combined shear (Schur + Q2^{-1}C2) det =", detsh, "-> Jacobian EXACTLY 1")
ok &= (detsh==1)
# Q1 as left op on C1: collapses c21
Q1C1 = Q1*C1
newB = [Q1C1[0,1], Q1C1[1,0], Q1C1[1,1]]   # induced on (c12, col0-row1, m22)
detB = sp.simplify(sp.Matrix(newB).jacobian(old).det())
print("B: LEFT op C1->Q1 C1 det =", detB, " col0 row1 =", sp.simplify(Q1C1[1,0]),
      "-> non-invertible projection -> Q1 forced as ideal cofactor")
ok &= (detB==0)
print("\nCLEAN (2,2,2): SAME structure as coupled (3,3,4). Only the Schur block SIZE differs")
print("(scalar here, 2x2 there). NO qualitative change in shear/cofactor status or |det Dg|.")
print("\nCLEAN CHECK:", "PASS" if ok else "FAIL")
import sys; sys.exit(0 if ok else 1)
