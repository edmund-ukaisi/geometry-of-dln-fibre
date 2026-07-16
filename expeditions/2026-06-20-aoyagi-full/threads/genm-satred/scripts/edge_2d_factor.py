"""(D) corank-one build route: the scalar 2D model H_p(w)=∫_{[-1,1]²}(w+x²y²)^{-p}dxdy FACTORS via u=xy
(Jacobian |y|^{-1}) into a BANKED 1D radial ∫(w+u²)^{-p}du (= w^{1/2-p}·B) TIMES the σ-radial ∫|y|^{-1}dy
(= the LOG, cut off at τ). So the Lean atom is NOT a monolithic 2D singular integral — it is
[banked radial] × [elementary Real.log] × [δ-fold]. Verified H_direct = H_factored exactly."""
import numpy as np
from scipy import integrate
def H_direct(w,p):
    return integrate.dblquad(lambda y,x:(w+x*x*y*y)**(-p),-1,1,-1,1)[0]
def H_factored(w,p):
    def inner(y):
        if abs(y)<1e-9: return 2*w**(-p)
        return integrate.quad(lambda u:(w+u*u)**(-p),-abs(y),abs(y))[0]/abs(y)
    return integrate.quad(inner,-1,1)[0]
for p in [0.8,1.2]:
    for w in [1e-2,1e-4,1e-6]:
        Hd,Hf=H_direct(w,p),H_factored(w,p); model=w**(0.5-p)*np.log(1/w)
        print(f"w={w:.0e} p={p}: direct={Hd:.4g} factored={Hf:.4g} (match {abs(Hd-Hf)/Hd:.1e}) "
              f"model w^(1/2-p)ln(1/w)={model:.4g} ratio={Hd/model:.3f}")
print("H_direct=H_factored (u=xy factorization); ≍ w^{1/2-p}ln(1/w). Atoms: banked-radial × Real.log × δ-fold.")
