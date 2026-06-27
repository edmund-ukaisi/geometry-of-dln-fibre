#!/usr/bin/env python3
"""
verify_334_jacobian.py — re-derive the (3,3,4) chart's |det Dphi| EXACTLY from the Lean chartA/chartC
definitions, to ground the 'Jacobian = u0^{minAdm-1}' claim before generalising.

From RouteMLayerCoverGEL2.lean (the SORRY-FREE chart):
  chartA334 (u : Fin 21->R) : 3x3 =
    [[u1, u1*u2, u1*u3],
     [u4, u4*u2 + u0*u6, u4*u3 + u0*u7],
     [u5, u5*u2 + u0*u8, u5*u3 + u0*u9]]
  chartC334 (u) : 3x4 =
    [[u0 - (u2*u13+u3*u17), u0*u10 - (u2*u14+u3*u18),
      u0*u11 - (u2*u15+u3*u19), u0*u12 - (u2*u16+u3*u20)],
     [u13,u14,u15,u16],
     [u17,u18,u19,u20]]
  phi334 = paramsEquivFlat (chartParams334)  -- the flat reshape is a permutation (det 1).
The genuine chart map (flat->flat, modulo the det-1 reshape) is u |-> (the 21 entries of A,C above).
We compute the 21x21 Jacobian of (entries of chartA334, chartC334) wrt (u0..u20) and take |det|.
Lean claims |det| = |u0|^7 * |u1|^2. minAdm(3,3,4)=8, so u0-exponent 7 = minAdm-1.  VERIFY.
"""
import sympy as sp

u = sp.symbols('u0:21', real=True)

A = [
    [u[1], u[1]*u[2], u[1]*u[3]],
    [u[4], u[4]*u[2] + u[0]*u[6], u[4]*u[3] + u[0]*u[7]],
    [u[5], u[5]*u[2] + u[0]*u[8], u[5]*u[3] + u[0]*u[9]],
]
C = [
    [u[0] - (u[2]*u[13] + u[3]*u[17]), u[0]*u[10] - (u[2]*u[14] + u[3]*u[18]),
     u[0]*u[11] - (u[2]*u[15] + u[3]*u[19]), u[0]*u[12] - (u[2]*u[16] + u[3]*u[20])],
    [u[13], u[14], u[15], u[16]],
    [u[17], u[18], u[19], u[20]],
]

# the 21 chart-output coordinates, in SOME fixed order (the order only changes det by +-1)
out = []
for i in range(3):
    for j in range(3):
        out.append(A[i][j])
for i in range(3):
    for j in range(4):
        out.append(C[i][j])
assert len(out) == 21

J = sp.Matrix(21, 21, lambda r, c: sp.diff(out[r], u[c]))
det = sp.factor(sp.expand(J.det()))
print("det Dphi (factored) =", det)
print()
# compare to +- u0^7 * u1^2
target = u[0]**7 * u[1]**2
print("det / (u0^7 u1^2) =", sp.simplify(det / target))
print("  (should be a constant +-1 => |det| = |u0|^7 |u1|^2, u0-exponent 7 = minAdm-1 = 8-1)")
