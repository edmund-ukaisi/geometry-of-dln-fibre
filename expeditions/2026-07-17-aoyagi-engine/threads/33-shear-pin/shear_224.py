#!/usr/bin/env python3
"""SHEAR-PIN (2,2,4) heart: build the FULL chart map g end-to-end as an honest coordinate
substitution (radial blow-up of the 2x2 Delta-block, THEN a unipotent Schur reduction of the
reduced block with pivot normalized to 1), and compute |det Dg| by DIRECT symbolic determinant
(not by multiplying claimed factors). Confirms: pure monomial u^3, unit == 1, even WITH the
Schur shear folded into g.  All sympy exact.
"""
import sympy as sp
ok = True

# source coords of the innermost chart:
u = sp.symbols('u', positive=True)                 # exceptional coord (pivot direction of Delta)
e12,e21,e22 = sp.symbols('e12 e21 e22')            # projective ratios in the Delta blow-up chart
S = sp.Matrix(2,4, sp.symbols('s0:8'))             # S (2x4) untouched by the Delta resolution

# ---- STEP 1 (blow-up beta): radial blow-up of Delta (2x2, codim 4) in the d11-pivot chart ----
#   Delta = u * Dbar, Dbar = [[1, e12],[e21, e22]]   (pivot Dbar[0,0] normalized to 1)
# target coords produced by beta = the 4 Delta entries (d11,d12,d21,d22)
d11 = u
d12 = u*e12
d21 = u*e21
d22 = u*e22
src_beta = [u, e12, e21, e22]
tgt_beta = [d11, d12, d21, d22]
Jbeta = sp.Matrix(tgt_beta).jacobian(src_beta)
det_beta = sp.simplify(Jbeta.det())
print("STEP1 blow-up beta: |det Dbeta| =", det_beta, " (expect u**3)")
ok &= (sp.simplify(det_beta - u**3) == 0)

# ---- STEP 2 (Schur reduction sigma of the REDUCED block Dbar, pivot = 1) ----
#   Dbar = [[1,e12],[e21,e22]];  unipotent Q1=[[1,0],[-e21,1]], Q2=[[1,-e12],[0,1]]
#   Q1 Dbar Q2 = diag(1, e22 - e21 e12).  As a COORDINATE change on the source it rewrites
#   e22 -> w := e22 - e21*e12 (a shear; e12,e21 kept).  Its Jacobian:
w = sp.symbols('w')                                # fresh atomic residual coord
wexpr = e22 - e21*e12
src_sigma = [u, e12, e21, e22]
tgt_sigma = [u, e12, e21, wexpr]                   # sigma rewrites the residual coord e22->w
det_sigma = sp.simplify(sp.Matrix(tgt_sigma).jacobian(src_sigma).det())
print("STEP2 Schur shear sigma (pivot=1): |det Dsigma| =", det_sigma, " (expect 1)")
ok &= (det_sigma == 1)

# ---- COMPOSITE g : maps innermost coords (u, e12, e21, w, S) all the way OUT to Delta,S entries.
#   invert the shear: e22 = w + e21*e12 ; then Delta = u*[[1,e12],[e21, w+e21 e12]] ----
innermost = [u, e12, e21, w] + list(S)
Delta_full = sp.Matrix([[u, u*e12],[u*e21, u*(w + e21*e12)]])
targets = list(Delta_full) + list(S)
Jg = sp.Matrix(targets).jacobian(innermost)
det_g = sp.simplify(Jg.det())
print("COMPOSITE g (blow-up + folded Schur shear): |det Dg| =", sp.factor(det_g), " (expect u**3)")
ok &= (sp.simplify(det_g - u**3) == 0 or sp.simplify(det_g + u**3) == 0)
print("        |det Dg| is a PURE MONOMIAL (unit == 1); the folded Schur shear added NOTHING.")

# ---- IDEAL side: <Delta S> pulls back; the leftover left factor is the cofactor ----
# Delta S = u * Dbar * S ; Dbar = Q1^{-1} diag(1,w) Q2^{-1}  (Q1 left cofactor survives)
Q1 = sp.Matrix([[1,0],[-e21,1]]); Q2 = sp.Matrix([[1,-e12],[0,1]])
Dbar = sp.Matrix([[1,e12],[e21, w+e21*e12]])
check = sp.simplify(Q1.inv()*sp.diag(1,w)*Q2.inv() - Dbar)
print("IDEAL  Dbar == Q1^{-1} diag(1,w) Q2^{-1} :", check == sp.zeros(2,2),
      " ; det Q1^{-1}=", sp.simplify(Q1.inv().det()))
ok &= (check == sp.zeros(2,2))

print("\n(2,2,4) HEART SHEAR-PIN:", "PASS" if ok else "FAIL")
import sys; sys.exit(0 if ok else 1)
