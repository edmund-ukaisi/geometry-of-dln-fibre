"""
Vertical-slice PART 3 (decisive): the corner blow-up that turns the two per-boundary radials
(charges 4,3) into ONE terminal divisor of threshold 7/2 -- the min-vs-sum resolution.

CORRECTED model (Codex-confirmed, decorrelated): after peeling boundary 0 (radial u0, codim 4)
and boundary 1 (radial u1, codim 3), the binding local model is a SUM

        G = u0^2 * U0  +  u1^2 * U1          (U0, U1 > 0 analytic units)

with measure factor  |u0|^{4-1} |u1|^{3-1} du0 du1 = |u0|^3 |u1|^2 du0 du1.

The two divisors {u0=0}, {u1=0} SEPARATELY give thresholds 4/2=2 and 3/2 -- the naive undershoot
min(2, 3/2) = 3/2.  The binding zero is the CORNER u0=u1=0.  Blowing up the corner accumulates the
Jacobian power while keeping loss order 2.
"""
import sympy as sp
c = sp.Symbol('c', positive=True)
u0, u1, tau, sig = sp.symbols('u0 u1 tau sigma', positive=True)
U0, U1 = sp.symbols('U0 U1', positive=True)   # bounded-below units

# ---- naive per-divisor thresholds (the undershoot) --------------------------
print("NAIVE (independent divisors), measure |u0|^3|u1|^2, loss order 2 each:")
print("   {u0=0}: 3-2c > -1 => c < 2      {u1=0}: 2-2c > -1 => c < 3/2")
print("   => min = 3/2   (r1upper-derisk undershoot / min-vs-sum WALL)\n")

# ---- corner blow-up chart A:  u1 = u0*tau  (covers u0 >= u1) ----------------
# measure: |u0|^3 |u1|^2 du0 du1 ; sub u1=u0 tau, du1 = u0 dtau (Jacobian u0)
meas_A = u0**3 * (u0*tau)**2 * u0                    # = u0^{3+2+1} tau^2
G_A    = u0**2 * U0 + (u0*tau)**2 * U1               # = u0^2 (U0 + tau^2 U1)
print("CHART A  u1 = u0*tau :")
print("   measure exponent of u0:", sp.degree(sp.Poly(meas_A, u0)), "(=6=Mval-1); tau power:",
      sp.degree(sp.Poly(meas_A, tau)))
G_A_fac = sp.factor(G_A)
print("   G =", G_A_fac, " -> loss order in u0 =", 2, "(u0^2 * unit, unit = U0+tau^2 U1 > 0)")
# integrand (G)^{-c} * measure ; u0-part: u0^{6 - 2c}
print("   u0-integral:  6 - 2c > -1  <=>  c < 7/2   (THE ACCUMULATED THRESHOLD)")
# tau-integral near tau in [0,1]: (U0+tau^2 U1)^{-c} * tau^2  -- bounded since U0>0, so finite all c
print("   tau-integral over [0,1]: integrand ~ (U0+tau^2 U1)^{-c} tau^2, U0>0 => bounded => finite for all c")

# ---- corner blow-up chart B:  u0 = u1*sigma  (covers u1 >= u0) --------------
meas_B = (u1*sig)**3 * u1**2 * u1                    # sub u0=u1 sigma, du0 = u1 dsigma
G_B    = (u1*sig)**2 * U0 + u1**2 * U1               # = u1^2 (sigma^2 U0 + U1)
print("\nCHART B  u0 = u1*sigma :")
print("   measure exponent of u1:", sp.degree(sp.Poly(meas_B, u1)), "(=6=Mval-1); sigma power:",
      sp.degree(sp.Poly(meas_B, sig)))
print("   G =", sp.factor(G_B), " -> loss order in u1 = 2")
print("   u1-integral:  6 - 2c > -1  <=>  c < 7/2")
print("   sigma-integral over [0,1]: (sigma^2 U0 + U1)^{-c} sigma^3, U1>0 => bounded => finite for all c")

# ---- exact confirmation via a concrete convergent integral (U0=U1=1) --------
# I(c) = ∫_0^1 ∫_0^1 (u0^2 + u1^2)^{-c} |u0|^3 |u1|^2 du0 du1  should be finite iff c < 7/2.
# Compute the abscissa symbolically via the corner charts (sum of the two).
print("\nEXACT check (U0=U1=1):  I(c) = ∫∫_[0,1]^2 (u0^2+u1^2)^{-c} u0^3 u1^2 du0 du1")
# chart A contribution: ∫_0^1 ∫_0^1 (u0^2(1+tau^2))^{-c} u0^6 tau^2 du0 dtau
IA_u0 = sp.integrate(u0**(6-2*c), (u0,0,1))            # = 1/(7-2c) for c<7/2
IA_tau = sp.integrate((1+tau**2)**(-c)*tau**2, (tau,0,1))
print("   chart A:  ∫u0^{6-2c}du0 =", IA_u0, "  (finite iff 7-2c>0 iff c<7/2)")
print("             ∫(1+tau^2)^{-c} tau^2 dtau over [0,1] is a finite number for every c (integrand bounded).")
# numeric abscissa demo
import mpmath as mp
def Inum(cval):
    f = lambda x,y: (x*x+y*y)**(-cval) * x**3 * y**2
    return mp.quad(lambda x: mp.quad(lambda y: f(x,y), [0,1]), [0,1])
for cval in [3.0, 3.4, 3.49, 3.51, 3.6, 4.0]:
    try:
        val = Inum(cval)
        print(f"   c={cval}:  I ~ {float(val):.4g}   {'(finite)' if val<1e6 else '(DIVERGING)'}")
    except Exception as e:
        print(f"   c={cval}:  divergent/overflow ({type(e).__name__})")
