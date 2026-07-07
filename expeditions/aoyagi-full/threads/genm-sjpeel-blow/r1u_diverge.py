import numpy as np
from scipy import integrate
# rank-1 Q top-row only: F ∝ ∫_{[-1,1]^{M0}} (∑_i x_i^2)^{-c'} dx (first column), finite iff c'<M0/2
for M0,cp in [(2,0.8),(2,1.0),(2,1.5),(3,1.0),(3,1.5)]:
    from scipy.special import gamma
    volS=2*np.pi**(M0/2)/gamma(M0/2)
    # radial ∫_0^1 r^{M0-1} r^{-2c'} dr = ∫_0^1 r^{M0-1-2c'} dr, finite iff M0-1-2c' > -1
    # i.e. M0-2c' > 0 i.e. c' < M0/2 STRICT (at c'=M0/2 the exponent is -1, ∫r^{-1} diverges logarithmically)
    conv = (M0-2*cp)>0
    print(f"M0={M0} c'={cp}: exponent M0-1-2c'={M0-1-2*cp:.2f} -> {'CONVERGES' if conv else 'DIVERGES'} (need c'<M0/2={M0/2})")
