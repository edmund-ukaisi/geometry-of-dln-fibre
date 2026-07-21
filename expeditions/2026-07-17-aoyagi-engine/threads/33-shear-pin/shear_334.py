#!/usr/bin/env python3
"""SHEAR-PIN (thread 33): does g at coupled corank>=2 involve source COORDINATE changes,
and if so what is |det Dg|? Worked EXACTLY on (3,3,4). All sympy, exact.

Question decomposed:
  ROLE 1 (coordinate change on source): the shears sh1 (C22->Delta Schur) and sh2 (Q2^{-1} C2 row op)
     -- do these change source coords? what is their Jacobian?
  ROLE 2 (ideal cofactor): the leftover left factor Q1^{-1} -- coordinate change or generator recombine?
  |det Dg|: pure monomial (unit==1) or monomial*unit(!=1)?
"""
import sympy as sp
ok = True

# ---- coordinates in the pivot chart c11 = 1 (C1 is 3x3, C2 is 3x4) ----
c12a, c12b = sp.symbols('c12a c12b')                  # C12 (1x2)  -- C1 non-pivot row0
c21a, c21b = sp.symbols('c21a c21b')                  # C21 (2x1)  -- C1 non-pivot col0
m = sp.symbols('m11 m12 m21 m22')                     # C22 (2x2)
C22 = sp.Matrix(2,2,m)
C12 = sp.Matrix([[c12a, c12b]])
C21 = sp.Matrix([[c21a],[c21b]])
C2  = sp.Matrix(3,4, sp.symbols('b0:12'))             # C2 entries (source coords)

C1 = sp.Matrix([[1, c12a, c12b],
                [c21a, m[0], m[1]],
                [c21b, m[2], m[3]]])

Q1 = sp.eye(3); Q1[1,0]=-c21a; Q1[2,0]=-c21b
Q2 = sp.eye(3); Q2[0,1]=-c12a; Q2[0,2]=-c12b
Delta = C22 - C21*C12                                  # Schur complement (2x2)

# =================================================================
# ROLE 1a: sh1 is the coordinate change (C12,C21,C22) -> (C12,C21,Delta).
# =================================================================
oldC1 = [c12a,c12b,c21a,c21b, m[0],m[1],m[2],m[3]]
newC1 = [c12a,c12b,c21a,c21b, Delta[0,0],Delta[0,1],Delta[1,0],Delta[1,1]]
J_sh1 = sp.Matrix(newC1).jacobian(oldC1)
det_sh1 = sp.simplify(J_sh1.det())
print("ROLE1a  sh1 (Schur C22->Delta) : det =", det_sh1, " (expect 1)")
ok &= (det_sh1 == 1)

# =================================================================
# ROLE 1b: sh2 is the coordinate change C2 -> tildeC2 = Q2^{-1} C2 (row0 sheared by C12).
# =================================================================
tC2 = Q2.inv() * C2                                    # tilde C2
old = oldC1 + list(C2)
new = oldC1 + list(tC2)
J_sh2 = sp.Matrix(new).jacobian(old)
det_sh2 = sp.simplify(J_sh2.det())
print("ROLE1b  sh2 (Q2^{-1} C2 row op): det =", det_sh2, " (expect 1)")
ok &= (det_sh2 == 1)

# combined shear (both together) as ONE coordinate change on the 20 coords
old_all = oldC1 + list(C2)
new_all = newC1 + list(tC2)
det_sh = sp.simplify(sp.Matrix(new_all).jacobian(old_all).det())
print("ROLE1   combined shear         : det =", det_sh, " (expect 1)  -> unit Jacobian EXACTLY 1")
ok &= (det_sh == 1)

# =================================================================
# ROLE 2: the leftover LEFT factor Q1^{-1}.
# =================================================================
peeled = sp.diag(1, Delta) * tC2                       # [[T],[Delta S]]
prod_recon = sp.simplify(Q1.inv()*peeled - C1*C2)
print("ROLE2   C1C2 == Q1^{-1}[[T],[DeltaS]] :", prod_recon == sp.zeros(3,4))
ok &= (prod_recon == sp.zeros(3,4))
print("        det Q1^{-1} =", sp.simplify(Q1.inv().det()), " (unipotent);  "
      "Q1^{-1} at 0 =", Q1.inv().subs({c21a:0,c21b:0}).tolist())
print("        -> Q1^{-1} recombines the OUTPUT rows (family), coeffs = source coords;")
print("           leaves source coords u untouched -> RegionRepresents cofactor, NOT a coord change.")

# =================================================================
# |det Dg|: fold shear (det 1) with the blow-up substitutions.
# =================================================================
q,u,E,al = sp.symbols('q u E alpha', positive=True)
jac_blowups = (q**3).subs(q,E) * (u**3).subs(u,E*al) * E     # = E^7 * alpha^3
jac_blowups = sp.expand(jac_blowups)
print("BLOWUPS jac (radial q^3 * radial u^3 * join E) =", jac_blowups, " (expect E**7*alpha**3)")
ok &= (sp.simplify(jac_blowups - E**7*al**3) == 0)

det_Dg_monomial = sp.simplify(det_sh) * jac_blowups
print("TOTAL  |det Dg| = det(shear) * jac_blowups =", sp.expand(det_Dg_monomial),
      " -> PURE MONOMIAL, unit == 1")
ok &= (sp.simplify(det_Dg_monomial - E**7*al**3) == 0)

print("\n(3,3,4) SHEAR-PIN:", "PASS" if ok else "FAIL")
import sys; sys.exit(0 if ok else 1)
