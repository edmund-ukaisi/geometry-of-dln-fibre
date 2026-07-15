"""
Confirm the mechanism: RLCT of the seam model = min over components of (codim/2), each component normal-crossing.
Model f=|H|^2+|FE|^2, H in R^2, F in R^2, E in R. Zero set = {H=0,E=0} (codim 3) U {H=0,F=0} (codim 4).
Importance-sampled threshold via tube of f: vol{f<=eps^2} ~ eps^{2*RLCT}. RLCT should be 3/2 -> exponent 3.
Sample H small (importance), F,E O(1) for the low-codim core.
"""
import numpy as np
np.random.seed(11)
def tube_f_exp(N=8_000_000):
    H=np.random.uniform(-1,1,(N,2)); F=np.random.uniform(-1,1,(N,2)); E=np.random.uniform(-1,1,(N,1))
    f=(H**2).sum(1)+((F**2).sum(1))*(E[:,0]**2)
    eps2=np.array([1e-4,4e-4,1.6e-3,6.4e-3])  # eps^2
    P=np.array([(f<=e).mean() for e in eps2])
    m=P>0
    # vol{f<=eps^2} ~ (eps^2)^{RLCT}; slope of logP vs log(eps^2) = RLCT
    slope=np.polyfit(np.log(eps2[m]),np.log(P[m]),1)[0] if m.sum()>=2 else float('nan')
    return slope,P
sl,P=tube_f_exp()
print(f"(2,2,2) seam model f=|H|^2+|FE|^2: RLCT-estimate(slope of vol{{f<=t}} vs t)={sl:.3f}  (expect 1.5=CR/2)")
print("  P=",['%.3e'%x for x in P])

# control: pure normal-crossing g=|H|^2+E^2 (codim 3), RLCT should be 3/2 too
def tube_g_exp(N=8_000_000):
    H=np.random.uniform(-1,1,(N,2)); E=np.random.uniform(-1,1,(N,1))
    g=(H**2).sum(1)+E[:,0]**2
    eps2=np.array([1e-4,4e-4,1.6e-3,6.4e-3])
    P=np.array([(g<=e).mean() for e in eps2]); m=P>0
    return np.polyfit(np.log(eps2[m]),np.log(P[m]),1)[0]
print(f"control g=|H|^2+E^2 (codim 3): RLCT-est={tube_g_exp():.3f} (expect 1.5)")
