import sympy as sp
u0,tau2,tau3,c = sp.symbols('u0 tau2 tau3 c', positive=True)

# 3-level NESTED corner (double-induction unrolled twice): dims a,b,e.
# scales: outer u0 (freed, dim a); u1=u0*tau2 (reduced level-1, dim b); u2=u1*tau3=u0*tau2*tau3 (reduced level-2, dim e).
# Loss F = u0^2 U0 + u1^2 U1 + u2^2 U2 = u0^2 ( U0 + tau2^2(U1 + tau3^2 U2) )  [nested, units U*>0]
# Jacobian (block radials u0^{a-1} u1^{b-1} u2^{e-1}) + substitution du0 du1 du2 = u0 * (u0 tau2) * du0 dtau2 dtau3 ... track powers:
#   u1=u0 tau2 -> du1 = u0 dtau2 (+ tau2 du0); u2=u0 tau2 tau3 -> du2 = u0 tau2 dtau3 (+ ...). Corner Jacobian |∂(u0,u1,u2)/∂(u0,tau2,tau3)| = u0 * (u0 tau2) = u0^2 tau2.
# integrand = u0^{a-1} (u0 tau2)^{b-1} (u0 tau2 tau3)^{e-1} * [u0^2 tau2] * F^{-c}
#   u0 power: (a-1)+(b-1)+(e-1)+2 = a+b+e-1
#   tau2 power: (b-1)+(e-1)+1 = b+e-1 ; tau3 power: e-1
#   F = u0^2 * G,  G = U0+tau2^2(U1+tau3^2 U2)  (units, bounded below by U0>0)
# => integrand = u0^{a+b+e-1-2c} * tau2^{b+e-1} * tau3^{e-1} * G^{-c}
for (a,b,e) in [(4,3,0+1),(2,2,2),(1,5,3)]:
    print(f"[nested a={a} b={b} e={e}]  u0-exp = {a+b+e}-1-2c ⟹ c < {sp.Rational(a+b+e,2)} = ½(a+b+e).  tau2-exp={b+e-1}(≥0), tau3-exp={e-1}(≥0): inner integrals finite (units G≥U0>0).")
print("  ⟹ NESTED corner piles ALL dims onto the outer radial u0; threshold = ½Σdims = ½minAdm(M). Inner ratio-integrals finite ⟸ units sector.\n")

# UNITS-DEPENDENCE of the tau-integral (the sector gate): if U0 -> 0 (rank drop), the tau-integral can diverge.
tau,c2 = sp.symbols('tau c2', positive=True)
b=3
# units U0=1: finite
val_unit = sp.integrate(tau**(b-1)*(1+tau**2)**(-sp.Rational(7,2)), (tau,0,1))
print(f"[tau-int, U0=1 (units), b={b}, c=7/2]  ∫τ^{b-1}(1+τ²)^-c dτ = {sp.nsimplify(val_unit)}  FINITE")
# units U0=eps->0 (near rank drop): integrand ~ (eps+tau^2)^{-c}; behaves like tau^{-2c} for tau>>sqrt(eps): needs b-2c>-1 ⟹ diverges for c>=b/2
eps=sp.symbols('eps',positive=True)
print(f"[tau-int, U0=eps→0]  (eps+τ²)^-c ~ τ^{{-2c}} for τ≫√eps ⟹ ∫τ^{{b-1-2c}} diverges for c≥b/2={b/2}  → the SMALL-σ_min complement is NOT in the units sector; it RECURSES (dmcheck P3).")
