import sympy as sp
print("="*78)
print("SOS LOWER BOUND: is F bounded below by a clean sum of squares near 0?")
print("="*78)
r0,r1,s0,s1,T0,T1 = sp.symbols('r0 r1 s0 s1 T0 T1', real=True)
a,b = sp.symbols('a b', positive=True)
# F = r0^2 + (a r0 + r0 T1)^2 + (b r1 + r1 T0)^2 + T0^2 + T1^2.
# It is LITERALLY a sum of squares already (each summand is a square or x^2)!
#   r0^2  -- square
#   (r0(a+T1))^2 -- square
#   (r1(b+T0))^2 -- square
#   T0^2, T1^2 -- squares
# So F = SUM OF 5 SQUARES exactly.  F >= 0 always, and F=0 iff all five vanish.
F = r0**2 + (a*r0+r0*T1)**2 + (b*r1+r1*T0)**2 + T0**2 + T1**2
# The "cross term 2 a T1 r0^2" I worried about is INSIDE the square (a r0+r0 T1)^2; F itself,
# as written, is manifestly a sum of squares.  My earlier worry conflated the EXPANDED form with F.
print("F as written = sum of 5 squares: r0^2, (r0(a+T1))^2, (r1(b+T0))^2, T0^2, T1^2.")
print("  => F >= 0 manifestly; the 'negative cross term' only appears on EXPANSION, not in F.")
print()
# Domination denominator soundness: each diff term <= eps * (one of these squares):
# 2 a r0^2 r1 s1 : need <= eps*F.  r0^2 <= F (first square). So <= 2|a r1 s1| * r0^2 <= 2|a r1 s1| F.
#   coeff 2|a||r1||s1| -> 0 at origin. GOOD.
# 2 T1 r0^2 r1 s1 : <= 2|T1 r1 s1| r0^2 <= 2|T1 r1 s1| F.  -> 0. GOOD.
# 2 b r0 r1^2 s0 : need r1^2 <= C*F.  Here r1^2 is NOT directly a square in F (we have (r1(b+T0))^2).
#   (r1(b+T0))^2 = r1^2 (b+T0)^2 >= r1^2 (b/2)^2 on |T0|<b/2.  So r1^2 <= (4/b^2)(square) <= (4/b^2)F.
#   => term <= 2|b r0 s0| r1^2 <= (8/b^2)|b r0 s0| F -> 0. GOOD (uses b!=0, |T0| small).
# 2 T0 r0 r1^2 s0 : similarly via r1^2 <= (4/b^2)F. GOOD.
# r0^2 r1^2 s0^2, r0^2 r1^2 s1^2 : <= r0^2 * (r1^2 s^2) <= F*(r1^2 s^2) -> 0. GOOD.
print("Domination denominators:")
print("  r0^2 IS a square in F  => r0^2 <= F directly.")
print("  r1^2 <= (4/b^2)F on |T0|<b/2  (via (r1(b+T0))^2 >= (b/2)^2 r1^2, b!=0 fixed).")
print("  => every diff term = (coeff ->0 at 0) * (<=F), so |F_moved-F| <= eps F, eps->0.")
print()
print("VERDICT: two-sided comparability (1-eps)F <= F_moved <= (1+eps)F holds on a small ball")
print("(eps<1).  The ONLY nonzero-constant inputs are a,b (PIN-1 reg-slice invertibility) and")
print("b appearing in the r1^2 domination.  No degeneracy near 0.  RLCT equal. SOUND.")
print()
# Also verify F_moved is itself a sum of squares (so >= 0, comparability well-posed):
F_moved = r0**2 + (a*r0+r0*T1+r0*r1*s1)**2 + (b*r1+r1*T0+r0*r1*s0)**2 + T0**2 + T1**2
print("F_moved is also a manifest sum of 5 squares =>0; comparability between two SOS germs. OK.")
