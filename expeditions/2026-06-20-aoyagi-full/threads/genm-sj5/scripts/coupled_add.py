import sympy as sp

# ============================================================================
# The coupled-corner "charges ADD" at the exact saturation, vs the naive split.
# Model (units sector): freed block dim a (radial u0), reduced structure dim b
# (radial u1), both units U0,U1 >0 bounded below. Loss F = u0^2 U0 + u1^2 U1.
# Jacobian (block radials): u0^{a-1} u1^{b-1}.  We test finiteness of
#   I(c') = ∫_0^1 ∫_0^1 (u0^2 U0 + u1^2 U1)^{-c'} u0^{a-1} u1^{b-1} du0 du1.
# CLAIM: threshold = (a+b)/2  (charges ADD).  Naive "drop u1" gives a/2.
# ============================================================================

u0,u1,tau,c = sp.symbols('u0 u1 tau c', positive=True)

def corner_threshold(a,b,U0=1,U1=1):
    # corner substitution on the sector u1<=u0:  u1 = u0*tau, tau in (0,1)
    # du0 du1 = u0 du0 dtau ; integrand u0^{a-1}(u0 tau)^{b-1} * u0 * (u0^2(U0+tau^2 U1))^{-c}
    #         = u0^{a+b-1-2c} * tau^{b-1} * (U0+tau^2 U1)^{-c}
    # tau-integral: finite (U0>0 bounded below, tau in (0,1)); u0-integral: ∫u0^{a+b-1-2c}du0<∞ ⟺ a+b-1-2c>-1 ⟺ c<(a+b)/2
    # (the reciprocal sector u0<=u1 gives (b+a)/2 by symmetry). Verify the tau-integral is finite & the exponent.
    expo = sp.Rational(a+b) - 1 - 2*c
    # tau integral value at generic c (units U0=U1=1):
    tau_int = sp.integrate(tau**(b-1)*(1+tau**2)**(-c), (tau,0,1))
    return expo, tau_int

for (a,b) in [(4,3),(1,1),(2,2),(3,5)]:
    expo, tint = corner_threshold(a,b)
    thr = sp.Rational(a+b,2)
    print(f"[corner a={a} b={b}] u0-exponent = {expo}; converges near 0 ⟺ c < {thr} = (a+b)/2 = ½·minAdm(add).  tau-int finite (units): {'yes' if tint.is_finite in (True,None) else tint}")

# Numeric confirmation of the FULL 2-block integral threshold via direct quadrature
import numpy as np
from scipy import integrate as si
def I2(a,b,c,U0=1.0,U1=1.0):
    f=lambda u1,u0:(u0**2*U0+u1**2*U1)**(-c)*u0**(a-1)*u1**(b-1)
    val,_=si.dblquad(f,1e-9,1.0,lambda u0:1e-9,lambda u0:1.0)
    return val
a,b=4,3
thr=(a+b)/2
for c_ in [thr-0.3, thr-0.05, thr+0.05, thr+0.3]:
    v=I2(a,b,c_)
    print(f"  a={a},b={b},c'={c_:.2f} (thr={thr}): I2={v:.4g}  {'FINITE' if c_<thr else 'DIVERGES-expected(grows as box→0 shrinks; check scaling)'}")

# naive "drop reduced" (freed block alone, U0 unit): ∫u0^{a-1-2c}du0 <∞ ⟺ c<a/2  (UNDERSHOOT)
print(f"\n[naive drop-reduced] freed block alone: c < {sp.Rational(a,2)} = a/2  << (a+b)/2={thr}  → UNDERSHOOT by b/2")
# naive Holder exponent-split at boundary: need c_f<a/2 AND c_r<b/2 with c_f+c_r=c=(a+b)/2 → impossible (sum of strict < = sum of bounds)
print(f"[naive Holder-split at c'=(a+b)/2={thr}] need c_f<{a/2} & c_r<{b/2}, c_f+c_r={thr}={a/2}+{b/2}: INFEASIBLE (strict sum cannot equal bound sum)")
