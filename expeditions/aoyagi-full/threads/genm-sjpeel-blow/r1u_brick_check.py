import numpy as np
from scipy import integrate
rng = np.random.default_rng(0)

# Check: residual-power matrix-fibre isotropic bound
# ∫_{[-1,1]^a} (w + ‖D‖²)^{-c'} dD ≤ Cresid_a(c') · w^{-(c'-a/2)}  (w>0, c'>a/2)
# and the full-space equality ∫_{ℝ^a}(w+‖D‖²)^{-c'} = w^{a/2-c'}·Cresid_a(c')
def Cresid(a, cp, N=200000):
    # ∫_{ℝ^a}(1+‖Q‖²)^{-c'} dQ, MC via importance? use polar: vol(S^{a-1})∫₀^∞ r^{a-1}(1+r²)^{-c'}dr
    from scipy.special import gamma
    volS = 2*np.pi**(a/2)/gamma(a/2)
    val,_ = integrate.quad(lambda r: r**(a-1)*(1+r**2)**(-cp), 0, np.inf)
    return volS*val

for (a,cp,w) in [(1,0.8,0.3),(2,1.5,0.2),(3,2.0,0.5),(4,3.0,0.7)]:
    if cp<=a/2: continue
    # full space integral via polar
    from scipy.special import gamma
    volS = 2*np.pi**(a/2)/gamma(a/2)
    full,_ = integrate.quad(lambda r: r**(a-1)*(w+r**2)**(-cp),0,np.inf)
    full*=volS
    pred = w**(a/2-cp)*Cresid(a,cp)
    print(f"a={a} c'={cp} w={w}: full={full:.4f} pred=w^(a/2-c')Cresid={pred:.4f} ratio={full/pred:.4f}")

# Check 1-D finite-cutoff: ∫₀^R (g²+z²h²)^{-c'} z^{a-1} dz  vs  g^{a-2c'} h^{-a} Φ(Rh/g)
print("--- 1D finite cutoff identity ---")
for (a,cp,g,h,R) in [(1,0.8,0.5,0.3,1.0),(2,1.5,0.4,0.6,1.0),(3,2.0,0.7,0.2,1.0)]:
    lhs,_=integrate.quad(lambda z:(g**2+z**2*h**2)**(-cp)*z**(a-1),0,R)
    Phi,_=integrate.quad(lambda u:u**(a-1)*(1+u**2)**(-cp),0,R*h/g)
    rhs=g**(a-2*cp)*h**(-a)*Phi
    print(f"a={a} c'={cp} g={g} h={h}: lhs={lhs:.5f} rhs={rhs:.5f} ratio={lhs/rhs:.5f}")
