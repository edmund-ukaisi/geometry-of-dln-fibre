"""
Clean (quadrature, not MC) confirmation of the binding corner M=(2,2,3), u=1,a=b=1:
 - corner RLCT = T1 = 2 exactly, via the radial integral  ∫_0^δ s^{3-2c'} ds
 - per-exponent K ~ 1/(T1 - c')  as c'->T1^-
 - the pointwise-in-z ratio R = G(z)/||Qp||^{-2q} stays bounded and shows K~1/(T1-c').
Front block is 3 scalars (p,beta,gamma); A_cor=(1,t2,t3). Use scipy nested quadrature.
"""
import numpy as np
from scipy import integrate

# ---- exact front integral F(s) = ∫_{[-1,1]^3} ((p+beta)^2 + beta^2 s^2 + gamma^2 s^2/(1+s^2))^{-q} ----
def F_front(s, q):
    c = s**2/(1+s**2)
    # integrate over gamma first (analytic-ish via quad), then beta, then p. Use dblquad+quad nesting.
    FL=1e-13
    def inner_gamma(p, beta):
        A = (p+beta)**2 + beta**2*s**2
        # ∫_{-1}^1 (A + c*gamma^2)^{-q} dgamma  (floor the integrable pivot-singular fiber)
        val,_ = integrate.quad(lambda g: (A + c*g*g + FL)**(-q), -1, 1, limit=80)
        return val
    val,_ = integrate.dblquad(inner_gamma, -1,1, -1,1, epsabs=1e-7, epsrel=1e-5)
    return val

print("=== corner front integral F(s) and small-s exponent (predict F ~ s^{1-2q}) ===")
for cprime in [1.7, 1.85, 1.95]:
    q = cprime-0.5
    ss=[0.16,0.08,0.04,0.02]
    Fs=[F_front(s,q) for s in ss]
    slope=np.polyfit(np.log(ss),np.log(Fs),1)[0]
    print(f"  c'={cprime} q={q:.2f}: F-slope={slope:+.4f}  predict 1-2q={1-2*q:+.4f}")

# ---- full corner G = ∫_0^delta det^{-1/2} F(s) (2*pi*s) ds  (polar over t=(t2,t3), |t|=s) ----
# det(QbQb^T)=1+s^2 ; Qb=(1,t2,t3). (approx alpha1=1; the alpha1 integration is a bounded factor)
def G_corner(q, delta=1.0):
    integrand = lambda s: (1+s**2)**(-0.5)*F_front(s,q)*(2*np.pi*s)
    val,_ = integrate.quad(integrand, 1e-4, delta, limit=200)
    return val

print("\n=== corner G(c') and per-exponent K~1/(T1-c'), T1=2 ===")
for cprime in [1.5,1.7,1.85,1.92,1.96]:
    q=cprime-0.5
    G=G_corner(q)
    # ||Qp||^2 = ||e1||^2 = 1, so R=G ; expect G*(T1-c') ~ const (radial ∫ s^{3-2c'} ~ 1/(4-2c')=1/(2(T1-c')))
    print(f"  c'={cprime}: G={G:.4e}   G*(T1-c')={G*(2-cprime):.4e}  (should approach a const as c'->2)")

print("\n=== radial exponent check: ∫_0^δ s^{3-2c'} ds converges iff c'<2 (=T1) ===")
for cprime in [1.5,1.9,1.99]:
    e=3-2*cprime
    conv = e>-1
    print(f"  c'={cprime}: exponent 3-2c'={e:+.2f} -> {'converges' if conv else 'DIVERGES'} ; ∫=1/(e+1)=1/(4-2c')={1/(4-2*cprime):.3f}")
