#!/usr/bin/env python3
"""
genM_genuine_4422.py — the GENUINE single-radial diffeo chart for (4,4,2,2), verified EXACTLY.

(4,4,2,2): factors A0 (4x4), A1 (4x2), A2 (2x2); F = ||A0 A1 A2||^2 (a 4x2 product).
Descent (4,2): A0,A1 full-rank clean (codim 0 each), minAdm=4 ENTIRELY from the leaf 2x2 block.
At the achiever the singular directions are the 4 entries of the deepest factor A2 (the leaf).

GENUINE CHART (mirrors phi334 = Schur-shear o radial blow-up, but here the descent has NO corank
residual to shear -- codims are 0 -- so it is a PURE radial blow-up of the deepest factor):
  blow up the 4-dim center {A2 = 0} by ONE radial coord u0:
       A2 = u0 * Abar2,   with Abar2 on a chart of the projective sphere (3 angular coords w),
  and keep A0, A1 as free O(1) coords.  This is the standard codim-4 blow-up:
       |det D(blowup)| = u0^{4-1} = u0^3 = u0^{minAdm-1}.   (radial coord exponent = codim - 1)
  F = ||A0 A1 (u0 Abar2)||^2 = u0^2 * ||A0 A1 Abar2||^2 = u0^2 * U,
       U = ||A0 A1 Abar2||^2,  bounded below on {A0=A1=I-ish, Abar2 = e1 direction} where the product
       is nonzero -- a positive-measure slice.

We verify EXACTLY:
  (1) F = u0^2 * U  (pure degree 2 in u0).
  (2) Jacobian of the chart map (A0 free, A1 free, A2 = u0*Abar2 with Abar2 = (w1,w2,w3, +-sqrt) OR
      the affine chart Abar2 = (1, w1, w2, w3)) has |det| = u0^3.
  (3) U bounded below on a positive-measure slice.
"""
import sympy as sp

# free coords
a0 = sp.Matrix(4, 4, lambda i, j: sp.Symbol(f'p{i}{j}', real=True))   # A0  (16)
a1 = sp.Matrix(4, 2, lambda i, j: sp.Symbol(f'q{i}{j}', real=True))   # A1  (8)
u0 = sp.Symbol('u0', positive=True)
# AFFINE blow-up chart for the 2x2 deepest factor: A2 = u0 * [[1, w1],[w2, w3]]
w1, w2, w3 = sp.symbols('w1 w2 w3', real=True)
Abar2 = sp.Matrix([[1, w1], [w2, w3]])
A2 = u0 * Abar2

P = a0 * a1 * A2     # 4x2
F = sp.expand(sum(P[i, j]**2 for i in range(4) for j in range(2)))

poly = sp.Poly(F, u0)
degs = sorted(set(m[0] for m in poly.monoms()))
print("(4,4,2,2) GENUINE radial chart (A2 = u0*[[1,w1],[w2,w3]], A0,A1 free):")
print("  F u0-degrees =", degs, " (want [2])")
U = poly.coeff_monomial(u0**2)
U = sp.expand(U)
print("  F = u0^2 * U exactly:", degs == [2])
print("  U = ||A0 A1 Abar2||^2  (u0-free):", not U.has(u0))

# (2) Jacobian: chart coords = (p.. 16) (q.. 8) (u0, w1, w2, w3) -> 28 = flatDim(4,4,2,2)?
# flatDim = 16+8+4 = 28.  chart input dims: 16+8+1+3 = 28.  Good.
# The chart map outputs the 28 flat entries (A0 entries, A1 entries, A2 entries).
# A0,A1 entries are identity in their coords (Jacobian block = I_24).  The A2 block:
#   A2 = [[u0, u0 w1],[u0 w2, u0 w3]]  as a function of (u0,w1,w2,w3).
A2vec = [A2[0, 0], A2[0, 1], A2[1, 0], A2[1, 1]]
J_A2 = sp.Matrix(4, 4, lambda r, c: sp.diff(A2vec[r], [u0, w1, w2, w3][c]))
detA2 = sp.factor(J_A2.det())
print("\n  A2-block Jacobian det =", detA2, " => |det of full chart| = |u0|^3 = |u0|^{minAdm-1}=u0^3:",
      sp.simplify(detA2 / u0**3) in (1, -1))

# (3) U bounded below on a positive-measure slice: take A0 = A1^T-ish so product nonzero.
# slice: a0 = I4 (first 4x4 identity-like), a1 = [[1,0],[0,1],[0,0],[0,0]], Abar2 col contributes.
# Evaluate U at a concrete slice point + small neighborhood.
slice_subs = {}
for i in range(4):
    for j in range(4):
        slice_subs[a0[i, j]] = 1 if i == j else 0
for i in range(4):
    for j in range(2):
        slice_subs[a1[i, j]] = 1 if i == j else 0
slice_subs[w1] = sp.Rational(0)
slice_subs[w2] = sp.Rational(0)
slice_subs[w3] = sp.Rational(1)
Uval = U.subs(slice_subs)
print("\n  U at slice (A0=I4, A1=[I2;0], Abar2=[[1,0],[0,1]]) =", Uval, " (>0 => bounded below near here)")
# show U as a sum of squares in general (it is ||M||^2 by construction, so >=0; nonzero on slice)
print("  U is a sum of squares (||A0 A1 Abar2||^2), so U>=0 and U>0 on the open slice neighborhood.")
