"""(D) (b−1)-block chart: general-a b=1 edge handled by dbuild's kit end-to-end.
Corank energy fragile (b=1) ~ (w+‖γ‖²‖z‖²)^{-p}, γ,z∈ℝ^a. Polar + u=rs:
 ∫r^{a-1}∫s^{a-1}(w+r²s²)^{-p} = [∫s^{-1}ds=log (sigmaLog)]×[∫u^{a-1}(w+u²)^{-p}du=w^{a/2-p}B (JapaneseBracket)].
So |y|⁻¹=s⁻¹ (sigmaLog) is from the u=rs coupling, NOT the minor-chart Gram (bounded). General b≥2:
the (b−1)-block minor chart peels the full-rank (b−1) block, leaving this b=1 FreeBilinear leaf."""
import numpy as np
from scipy import integrate
def H_direct(w,p,a):
    return integrate.dblquad(lambda s,r: r**(a-1)*s**(a-1)*(w+r*r*s*s)**(-p),0,1,0,1)[0]
def H_factored(w,p,a):
    def inner(s):
        if s<1e-9: return w**(-p)/a
        return integrate.quad(lambda u:u**(a-1)*(w+u*u)**(-p),0,s)[0]/(s**a)
    return integrate.quad(lambda s: s**(a-1)*inner(s),0,1)[0]
for a in [1,2,3]:
    p=a/2+0.3
    for w in [1e-3,1e-5]:
        print(f"a={a} p={p} w={w:.0e}: direct={H_direct(w,p,a):.4g} factored={H_factored(w,p,a):.4g} "
              f"(match) ~ w^(a/2-p)ln(1/w)")
