import sympy as sp
print("="*78)
print("RECONCILE: the zero-locus of dlnLoss(M) 0 is {∏A_s = 0} (product = 0, NOT rank rho>0).")
print("My rank-strata model was WRONG: a rank-rho>0 product point has loss>0, not on {loss=0}.")
print("So ALL singular points of |loss|^{-c} have product EXACTLY zero. The strata are by the")
print("rank pattern of the INDIVIDUAL factors / partial products, all giving product 0.")
print("="*78)
# Correct picture: loss = ||A0 A1 ... AL||^2.  {loss=0} = {A0...AL = 0}.  This is the ZERO-PRODUCT
# variety.  Its strata are indexed by the rank pattern (r1,...,rL) of partial products / the
# 'how the zero is achieved'.  The deepest (all A_s = 0) is ONE point; but there are MANY other
# points where the product is 0 without all factors 0 (e.g. A0=0 but A1..AL arbitrary; or A0 row in
# left-kernel of A1, etc).
#
# At such a non-all-zero point p in {product=0}, what is the LOCAL rlct of ||product||^2?
# This is the rlct of the multiplication-map fibre over 0 -- the paper's ACTUAL object.  The paper's
# theorem: rlct(dlnLoss, deepest) = (1/2) minAdm = (1/2) C where C = codim of the TOP stratum.
# The relevant question for box-collapse: among ALL points p of {product=0} INSIDE the ratio box,
# is the local rlct MINIMIZED at the deepest (all-zero) point?
#
# Test directly on (1,1,2): loss = s^2(b1^2+b2^2). {loss=0}={s=0}∪{b=0}.
s,b1,b2 = sp.symbols('s b1 b2', real=True)
L112 = s**2*(b1**2+b2**2)
print("\n(1,1,2): loss = s^2(b1^2+b2^2). Strata of {loss=0}:")
print("  all-zero (0,0,0): s^2(b1^2+b2^2). Newton: rlct=? compute below.")
print("  {s=0,b!=0} e.g (0,1,0): loss ~ s^2*(1) = s^2 -> rlct=1/2 (1 var).")
print("  {b=0,s!=0} e.g (1,0,0): loss ~ 1*(b1^2+b2^2) -> rlct=2/2=1.")
# rlct at all-zero of s^2(b1^2+b2^2): blow up. integrand |s|^{-2c}(b1^2+b2^2)^{-c}. 
# s-integral: c<1/2. b-integral (2D Morse-like ||b||^{-2c}): converges iff 2c<2 i.e c<1. min=1/2.
print("  all-zero rlct: |s|^{-2c} integ c<1/2 AND ||b||^{-2c} in R^2 integ c<1 => min = 1/2.")
print()
print("  => rlct: all-zero=1/2, {s=0,b!=0}=1/2 (TIE), {b=0,s!=0}=1. Deepest=1/2 is the MIN.")
print()
# The {s=0, b!=0} stratum TIES at 1/2.  Why: at (0, b0!=0), loss ~ s^2 ||b0||^2 ~ s^2, rlct of a
# single square in 1 var = 1/2 = SAME as deepest.  The deepest does NOT strictly beat it -- but
# does not LOSE to it.  Need: NO stratum goes BELOW deepest.  The deepest has the MAX number of
# vanishing directions => the smallest rlct.  Any sub-stratum has FEWER vanishing dirs => >= rlct.
print("STRUCTURAL CLAIM (correct version): at p in {product=0}, loss ~ (vanishing-monomial)·(units).")
print(" The number of independent vanishing directions is MAXIMAL at the all-zero point (all factors")
print(" degenerate simultaneously). Fewer factors vanishing => fewer vanishing dirs => LARGER rlct.")
print(" The all-zero point is the DEEPEST stratum of {product=0} (the unique closed orbit / cone tip).")
print(" => rlct(loss, p) >= rlct(loss, all-zero) for every p in {product=0}. Deepest = global min.")
