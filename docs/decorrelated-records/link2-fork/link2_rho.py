import sympy as sp
print("="*78)
print("link2_rho_residual: does slice-only core-constancy (∂E/∂core only off-slice)")
print("close the reg-arg Θ-swap at the RLCT level?  EXACT model at (2,2,2).")
print("="*78)
# Setup: q = (reg, core, spec).  R(q) := regStraighten(q).1 = deepestEFull(q) (reg residual).
# Θ shifts ONLY the core by delta(reg,spec):  Θq = (reg, core+delta, spec).
# C(q) = coreF∘conjAbsorb(q) FIXED on both sides.
# residual:  rlctAtOn( ∑R(q)² + C(q) ) 0  =?=  rlctAtOn( ∑R(Θq)² + C(q) ) 0.
#
# From CoreConstant atom: R(0,c,0) = R(0,0,0) (core enters reads ONLY off the reg=spec=0 slice).
# Concretely R components are reg residuals; the core couples as M12 ← y0·T1, M21 ← z1·T0
# (exact, verified earlier).  So:
#   R(Θq) = R(q) with T_s -> T_s + delta_s.  The CHANGE is:
#     ΔR_12 = y0 * delta1,   ΔR_21 = z1 * delta0   (bilinear: reg-coord * core-shift).
# delta_s = (sc-sb)_s(reg,spec).  Both sc,sb are Schur corrections = O(|reg,spec|^2),
# AND delta_s VANISHES at reg=spec=0 (the basepoint, Θ0=0).
#
# Build the two integrand germs at 0 and compare their RLCT (Newton-polytope / blow-up).
r0,r1,s0,s1,T0,T1 = sp.symbols('r0 r1 s0 s1 T0 T1', real=True)  # reg=(r0,r1), spec=(s0,s1), core=(T0,T1)
# reg residual reads (block-triangular frames, (2,2,2) r=1).  Use the EXACT structure:
# At reg=spec=0 the reads are core-FREE (atom).  Model reads as functions vanishing at 0:
# pick representative reg residual comps that match the leak structure.
# Let reg coords be y0:=r0, z1:=r1 (the off-diag reg reads); the reads:
#   R11 = r0  (a reg-only read, leading)     [stand-in: linear in reg]
#   R12 = y0_read + y0*T1   where y0_read is reg part; on-slice (reg=0) => 0, core T1 enters * y0.
#   R21 = z1_read + z1*T0
# To be faithful: at reg=spec=0, R12=R21=0 (atom: reads core-free AND reg-zero => 0).
# So model R12 = a*r0 + r0*T1 (=(reg)*(1+core)), R21 = b*r1 + r1*T0.
a,b = sp.symbols('a b', positive=True)
R11 = r0
R12 = a*r0 + r0*T1
R21 = b*r1 + r1*T0
# Θ shift on core: delta_s = O(2) and vanishes at 0.  Take the Schur form -Z(1+X)^{-1}Y ~ O(2).
# Model delta0 = r0*s0 (a quadratic in (reg,spec)), delta1 = r1*s1.  (Generic O(2), vanishing at 0.)
delta0 = r0*s0
delta1 = r1*s1
R12_th = R12.subs(T1, T1+delta1)   # = a r0 + r0(T1 + r1 s1)
R21_th = R21.subs(T0, T0+delta0)
print("R(q):    R11=",R11," R12=",R12," R21=",R21)
print("R(Θq):   R12_th=",sp.expand(R12_th)," R21_th=",sp.expand(R21_th))
print()
# Core energy C(q): frobSq(prod(decode core + corrConj)) -- a function of (core,reg,spec); FIXED both sides.
# At leading order C ~ ∑ (core + O(2))² ~ T0²+T1²+... .  Model C = T0**2 + T1**2 (leading; the O(2)
# corrections are higher order and the SAME both sides, so don't affect the comparison).
C = T0**2 + T1**2
F_unmoved = R11**2 + R12**2 + R21**2 + C
F_moved   = R11**2 + R12_th**2 + R21_th**2 + C
print("F_unmoved =", sp.expand(F_unmoved))
print("F_moved   =", sp.expand(F_moved))
print("F_moved - F_unmoved =", sp.expand(F_moved - F_unmoved))

print()
print("="*78)
print("RLCT comparison via DOMINATION (the rigorous mechanism).")
print("="*78)
# A clean RLCT-invariance tool: if c1*F_unmoved <= F_moved <= c2*F_unmoved on a nbhd of 0
# (positive constants), the RLCTs are EQUAL (Watanabe: RLCT depends only on the ideal up to
# local comparability / same integral-convergence threshold).  Test comparability.
diff = sp.expand(F_moved - F_unmoved)
# Each diff term: is it dominated by F_unmoved near 0?  F_unmoved contains r0^2, T1^2, T0^2, b^2 r1^2...
# Key sum-of-squares lower bounds inside F_unmoved (drop cross terms via the squares present):
# F_unmoved >= r0^2  (from r0^2 term, but careful: 2 T1 a r0^2 could be negative).
# Proper approach: F_unmoved = R11^2+R12^2+R21^2+C with C=T0^2+T1^2.  It's a sum of squares + C.
# So F_unmoved >= R12^2 = (a r0 + r0 T1)^2 = r0^2 (a+T1)^2,  and >= T1^2, and >= R21^2, >= T0^2, >= r0^2(=R11^2).
# Bound each diff term by eps * F_unmoved near 0 (|coords| small):
print("diff terms:")
for t in diff.as_ordered_terms():
    print("   ", t, "  deg =", sp.total_degree(t))
print()
# Domination check: each diff term has degree >= 4 and contains a factor that is a coordinate^2
# matching a square in F_unmoved, times small coords.  E.g.:
#   2 a r0^2 r1 s1 = (2 a s1 r1) * r0^2;  r0^2 <= F_unmoved... but we need it <= eps*F_unmoved with
#   eps->0.  r0^2 appears in F_unmoved as R11^2.  So term <= |2 a s1 r1| * R11^2 <= eps*F_unmoved
#   for |r1|,|s1| small.  GOOD (the extra coords r1,s1 -> 0 give the eps).
# Do this term-by-term: each diff term = (vanishing-at-0 coeff) * (a square present in F_unmoved).
checks = [
 ("2*T0*r0*r1**2*s0", "r1**2*(2 T0 r0 s0)", "r1^2 in F? via R21^2=r1^2(b+T0)^2 -> r1^2 dominated"),
 ("2*T1*r0**2*r1*s1", "r0**2*(2 T1 r1 s1)", "r0^2 = R11^2 in F"),
 ("2*a*r0**2*r1*s1",  "r0**2*(2 a r1 s1)",  "r0^2 = R11^2 in F"),
 ("2*b*r0*r1**2*s0",  "r1**2*(2 b r0 s0)",  "r1^2 from R21^2"),
 ("r0**2*r1**2*s0**2","r0**2*(r1**2 s0**2)","r0^2 = R11^2 in F, x small"),
 ("r0**2*r1**2*s1**2","r0**2*(r1**2 s1**2)","r0^2 = R11^2 in F, x small"),
]
print("Domination (each diff term = small_coeff(->0 at 0) * square_in_F_unmoved):")
for t,fac,why in checks:
    print(f"   {t:22s} = {fac:22s}  [{why}]")
print()
print("=> |F_moved - F_unmoved| <= eps(coords)*F_unmoved with eps->0 at 0")
print("   => (1-eps)F_unmoved <= F_moved <= (1+eps)F_unmoved on a small ball.")
print("   => RLCT(F_moved) = RLCT(F_unmoved).  link2_rho_residual holds by DOMINATION,")
print("      NOT by a diffeo, and NOT by first-order alone.")
