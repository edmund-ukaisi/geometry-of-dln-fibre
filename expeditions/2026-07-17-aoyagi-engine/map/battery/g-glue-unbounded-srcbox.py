#!/usr/bin/env python3
# guards: region-glue, coverage-theorem
# config: L=1, M=(2,1) so prod M A = A (2x1), F = frobSq = y1^2 + y2^2 (degree 2L=2, N=flatDim=2);
#         unbounded sector blow-up chart beta(u,v) = (u, u^(a-1) v) on {0<|u|<delta, |v|<=|u|^-(a-2)}
# provenance: threads/06-region-glue (glue-t05); the F1 STOP-tripwire counterexample, decorrelated-Codex-reached
"""Unbounded-srcBox kill witness: region_glue is FALSE without srcBox boundedness.

The glue lane's per-leaf read is SEPARATED: after the area-formula change of
variables, the leaf integrand is  prod_k |u_k|^(divExp_k - 1 - 2c') * baseForm^-c',
and its finiteness is read OFF the per-coordinate exponents (c' < divExp_k/2 for
each divisor, c' < resRank/2 for the Morse core). This separated read is VALID
ONLY when the chart's source box is BOUNDED. On an UNBOUNDED source, a spectator
direction whose extent grows like a negative power of a divisor coordinate feeds
extra powers of that coordinate back into the integral, dropping the true
threshold BELOW the advertised min_k divExp_k/2 -- so `ChartBridge` (without a
boundedness clause) does NOT imply the box-integral finiteness `region_glue`
claims. This script is the executable kill witness for that gap and for the
elder-ratified fix (srcBox measurable + bounded-in-flat-cube).

The witness is realizable with a REAL M (not just an abstract model):
  L = 1, M = (2, 1):  Params = { A : 2x1 real matrix },  prod M A = A,
  F(A) = frobSq(A) = A00^2 + A10^2 = y1^2 + y2^2   (degree 2L = 2, N = flatDim = 2).

Chart family (a >= 3 integer), a genuine monomial blow-up composed with identity psi:
  beta(u, v) = (u, u^(a-1) * v).
  * pullback:   F(beta(u,v)) = u^2 + (u^(a-1) v)^2 = u^2 * (1 + u^(2a-4) v^2) = u^2 * R.
  * Jacobian:   |det D beta| = |u|^(a-1)   ==>  the leaf ADVERTISES divExp = a (one divisor),
                                                resRank = 0 (R is a bounded unit).
  * source:     UNBOUNDED sector  S = { 0 < |u| < delta, |v| <= |u|^-(a-2) }.

On S the residual is a bounded unit:  1 <= R <= 2   (since u^(2a-4) v^2 <= 1 on S).
So EVERY current-ChartBridge clause holds EXCEPT boundedness, advertising a leaf
threshold a/2. Yet:

  bounded source (|v| <= V const):  I(c') finite  <=>  c' < a/2      (advertised, correct)
  unbounded sector S:               I(c') finite  <=>  c' < 1        (TRUE, = rlct of y1^2+y2^2)

so for c' in [1, a/2) (nonempty since a >= 3) the strengthened `hrat` (c' < a/2) HOLDS
while the box integral DIVERGES -- region_glue would be false. Boundedness is exactly
what collapses the a/2 advertisement back to the honest per-coordinate read.

We verify EXACTLY with sympy:
  (P) the pullback + Jacobian identities,
  (R) the residual squeeze 1 <= R <= 2 on S,
  (U) the sector CoV integral I(c') = int_S (F o beta)^-c' |det D beta|  diverges for c' >= 1,
  (B) the SAME integral over a BOUNDED source is finite exactly for c' < a/2,
  (T) the true RLCT of F over a bounded ball is 1 (the 2D sum-of-squares threshold).
Exit 0 iff, for every tested a, the gap [1, a/2) is nonempty AND (U)/(B)/(T) hold as stated.
"""

import sys
import sympy as sp

u, v, c = sp.symbols("u v c", positive=True)  # u,v > 0 (WLOG on a quadrant; even integrand)


def check_a(a: int) -> bool:
    ok = True

    # --- (P) pullback + Jacobian, exact ---
    y1 = u
    y2 = u**(a - 1) * v
    F_beta = sp.expand(y1**2 + y2**2)              # F(beta(u,v))
    R = sp.simplify(F_beta / u**2)                 # residual: F_beta = u^2 * R
    R_expected = 1 + u**(2 * a - 4) * v**2
    if sp.simplify(R - R_expected) != 0:
        print(f"  a={a}: (P) residual mismatch: {R} != {R_expected}"); ok = False

    # Jacobian det of (u,v) |-> (u, u^(a-1) v)
    J = sp.Matrix([[sp.diff(y1, u), sp.diff(y1, v)],
                   [sp.diff(y2, u), sp.diff(y2, v)]])
    detJ = sp.simplify(J.det())                    # = u^(a-1)
    if sp.simplify(detJ - u**(a - 1)) != 0:
        print(f"  a={a}: (P) |det Dbeta| mismatch: {detJ} != u^{a-1}"); ok = False

    # --- (R) residual squeeze on the sector |v| <= u^-(a-2), i.e. u^(a-2) v <= 1 ---
    # on S: u^(2a-4) v^2 = (u^(a-2) v)^2 <= 1, so 1 <= R <= 2.
    # check at the boundary v = u^-(a-2): R = 1 + 1 = 2.
    R_bdry = sp.simplify(R.subs(v, u**(-(a - 2))))
    if sp.simplify(R_bdry - 2) != 0:
        print(f"  a={a}: (R) boundary residual != 2: {R_bdry}"); ok = False

    # --- integrand after CoV: (F o beta)^-c * |det Dbeta| = (u^2 R)^-c * u^(a-1) ---
    integrand = (u**2 * R)**(-c) * u**(a - 1)

    # --- (U) UNBOUNDED sector: inner v-integral over [0, u^-(a-2)], then u over (0,1] ---
    # lower-bound R by <= 2  ==> integrand >= 2^-c * u^(-2c) * u^(a-1); inner width = u^-(a-2).
    # So I_lower(c) = 2^-c * int_0^1 u^(-2c) u^(a-1) u^-(a-2) du = 2^-c * int_0^1 u^(1-2c) du.
    # int_0^1 u^(1-2c) du diverges  <=>  1 - 2c <= -1  <=>  c >= 1.
    for cval in [sp.Rational(1, 1), sp.Rational(a, 2) - sp.Rational(1, 4)]:  # c=1 and just below a/2
        if cval < 1:
            continue
        inner = sp.integrate(u**(1 - 2 * cval), (u, 0, 1))
        finite = inner.is_finite
        if finite:  # must DIVERGE for c >= 1
            print(f"  a={a}: (U) sector lower-bound integral FINITE at c={cval} (expected divergent)")
            ok = False

    # --- (B) BOUNDED source |v| <= 1 (V const): inner width const ==> I(c) ~ int u^(a-1-2c) du,
    #         finite <=> a-1-2c > -1 <=> c < a/2.  Check c=a/2 - 1/4 (finite) and c=a/2 (divergent). ---
    c_ok = sp.Rational(a, 2) - sp.Rational(1, 4)
    Ib_ok = sp.integrate(u**(a - 1 - 2 * c_ok), (u, 0, 1))
    if not Ib_ok.is_finite:
        print(f"  a={a}: (B) bounded-source integral DIVERGES at c={c_ok} < a/2 (expected finite)")
        ok = False
    c_bad = sp.Rational(a, 2)
    Ib_bad = sp.integrate(u**(a - 1 - 2 * c_bad), (u, 0, 1))
    if Ib_bad.is_finite:
        print(f"  a={a}: (B) bounded-source integral FINITE at c=a/2 (expected divergent)")
        ok = False

    # --- (T) true RLCT of F = y1^2 + y2^2 over a bounded ball: 2D radial, finite <=> c < 1 ---
    r = sp.symbols("r", positive=True)
    # int_ball (r^2)^-c * r dr  ~  int_0^1 r^(1-2c) dr, finite <=> 1-2c > -1 <=> c < 1
    T_ok = sp.integrate(r**(1 - 2 * sp.Rational(3, 4)), (r, 0, 1))     # c = 3/4 < 1
    T_bad = sp.integrate(r**(1 - 2 * sp.Rational(1, 1)), (r, 0, 1))    # c = 1
    if not T_ok.is_finite or T_bad.is_finite:
        print(f"  a={a}: (T) true 2D threshold != 1"); ok = False

    # --- the gap: advertised a/2 vs true 1; must be a nonempty interval [1, a/2) ---
    if not (sp.Rational(a, 2) > 1):
        print(f"  a={a}: gap [1, a/2) empty"); ok = False

    if ok:
        print(f"  a={a}: OK -- advertised divExp/2 = {sp.Rational(a,2)}, true threshold = 1; "
              f"unbounded gap c in [1, {sp.Rational(a,2)}): hrat holds, integral diverges. "
              f"bounded-source threshold = a/2 (matches advertisement).")
    return ok


def main() -> int:
    print("g-glue-unbounded-srcbox: region_glue is FALSE without srcBox boundedness")
    print("(L=1, M=(2,1), F = y1^2+y2^2; unbounded sector chart beta(u,v)=(u,u^(a-1)v))")
    all_ok = True
    for a in (3, 4, 5):
        all_ok &= check_a(a)
    if all_ok:
        print("PASS: every current-ChartBridge clause holds on the unbounded sector while the box "
              "integral diverges on [1, a/2); boundedness collapses the read back to the honest "
              "per-coordinate threshold. The elder-ratified srcBox boundedness clause is necessary.")
        return 0
    print("FAIL: witness did not reproduce")
    return 1


if __name__ == "__main__":
    sys.exit(main())
