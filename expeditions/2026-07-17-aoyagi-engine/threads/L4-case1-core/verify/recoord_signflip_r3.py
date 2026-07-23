"""seat-L4D — verify Codex R3 (the head-question CORRECTION): the fix is a UNIPOTENT recoord
sign-flip (branch ii: A_{S+1}·Q₁ = −γ, NOT the baked A_{S+1}·Q₁⁻¹ = +γ), NOT a skeleton revision.

(2,2,2,2) ed1 corner pivot a=b=0. Confirms:
 - baked (+γ recoord): (A₁·A₀)[0][0] = u₁₀₀ + 2·u₀₁₀·u₁₀₁ (coeff-2 defect), jacDet 1.
 - flip recoord (−γ):  (A₁·A₀)[0][0] = u₁₀₀ (clean, extra-block coeff 0), jacDet 1 (hshear preserved).
CAVEAT (banked, NOT closed here): R3's residual (u₁₀₀) ≠ honest_clear's (w₁₀₀ = u₁₀₀+u₀₁₀u₁₀₁) — R3 is
boost-ready + ideal-preserving (unipotent automorphism) but does not literally match honest_clear; the
elder must rule whether the bar is "= honest_clear" or "boost-ready". Full residual / wide witnesses
((2,3,2),(2,3,2,2)) / interior pivot / branch-(i) Schur sign: NOT verified here (pnp harness + follow-up).
"""
import sympy as sp
u = lambda l, r, c: sp.Symbol(f'u{l}{r}{c}')
A0 = sp.Matrix([[u(0,0,0), u(0,0,1)], [u(0,1,0), u(0,1,1)]])
A1 = sp.Matrix([[u(1,0,0), u(1,0,1)], [u(1,1,0), u(1,1,1)]])
g, b = u(0,1,0), u(0,0,1)
allv = [u(0,0,0),u(0,0,1),u(0,1,0),u(0,1,1),u(1,0,0),u(1,0,1),u(1,1,0),u(1,1,1)]

def check(recoord_sign):
    img = {v: v for v in allv}
    img[u(0,1,1)] = u(0,1,1) - g*b                       # branch i Schur (unchanged)
    img[u(1,0,0)] = u(1,0,0) + recoord_sign*g*u(1,0,1)   # branch ii recoord, sign = recoord_sign
    img[u(1,1,0)] = u(1,1,0) + recoord_sign*g*u(1,1,1)
    J = sp.Matrix([[sp.diff(img[v], w) for w in allv] for v in allv]).det()
    A0m, A1m = A0.copy(), A1.copy()
    A0m[1,1] = img[u(0,1,1)]; A1m[0,0] = img[u(1,0,0)]; A1m[1,0] = img[u(1,1,0)]; A0m[0,0] = 1
    return sp.expand((A1m*A0m)[0,0]), sp.expand(J)

p_baked, J_baked = check(+1)
p_flip,  J_flip  = check(-1)
print('BAKED (+γ recoord): [0][0] =', p_baked, ' jacDet =', J_baked)
print('FLIP  (−γ recoord): [0][0] =', p_flip,  ' jacDet =', J_flip)
assert p_baked == u(1,0,0) + 2*u(0,1,0)*u(1,0,1) and J_baked == 1
assert p_flip == u(1,0,0) and J_flip == 1
print('\nR3 CONFIRMED (corner pivot): the −γ recoord flip is UNIPOTENT (jacDet 1) and clean.'
      '\nSo the head question resolves toward DEF-EDIT-3-REPRESENTABLE (sign flip), NOT skeleton-revision.'
      '\n(honest_clear-match + wide + interior + ideal: NOT closed here — see docstring caveat.)')
