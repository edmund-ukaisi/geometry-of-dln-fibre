import numpy as np
from numpy.polynomial.legendre import leggauss

# Multiplier M_a(g, sigma1, sigma2) = ∫_{[-1,1]^2} (g^2 + s1^2 y1^2 + s2^2 y2^2)^{-a/2} dy
# (Y in singular coords of B; s1,s2 = singular values of B). Decisive: scaling as g->0, s2->0.
# Codex overturn test: is M <= C log^N(1/g) (NO power loss -> revives single-chain reduction)
# or does it lose a power in g or s2 (-> joint (S,J) needed)?

xg,wg = leggauss(600)              # high-order GL on [-1,1]
def Ma(g, s1, s2, a):
    # 2D tensor GL quadrature
    Y1=xg[:,None]; Y2=xg[None,:]
    F=(g*g + (s1*Y1)**2 + (s2*Y2)**2)**(-a/2.0)
    return (wg[:,None]*wg[None,:]*F).sum()

print("=== (2,2,2,2) t=1: a=1, exponent -1/2, Y in R^2, B=A2 (2x2) ===")
print("Scaling of M vs g (at fixed small s2) and vs s2 (at fixed small g):\n")
print(" fix s1=1, s2=1e-4 (B nearly rank-1); vary g -> is M ~ log(1/g) or g^{-p}?")
gs=[1e-1,1e-2,1e-3,1e-4,1e-5,1e-6]
Ms=[Ma(g,1.0,1e-4,1) for g in gs]
for g,M in zip(gs,Ms): print(f"   g={g:.0e}: M={M:8.3f}   log(1/g)={np.log(1/g):6.2f}   M/log(1/g)={M/np.log(1/g):6.3f}")
# fit power: if M ~ g^{-p}, log M vs log g slope = -p. If log, slope ~0 (M grows like log).
import numpy as np
lg=np.log(gs); lM=np.log(Ms)
p=np.polyfit(lg,lM,1)[0]
print(f"   power-fit slope d(logM)/d(logg) = {p:.4f}  (0=>log/no-power ; -p<0 => power loss g^{{{p:.2f}}})")

print("\n fix s1=1, g=1e-5; vary s2 (B->rank1) -> is M ~ log(1/s2) or s2^{-p}?")
ss=[1e-1,1e-2,1e-3,1e-4,1e-5,1e-6]
Ms2=[Ma(1e-5,1.0,s2,1) for s2 in ss]
for s2,M in zip(ss,Ms2): print(f"   s2={s2:.0e}: M={M:8.3f}   log(1/s2)={np.log(1/s2):6.2f}")
ls=np.log(ss); lM2=np.log(Ms2)
p2=np.polyfit(ls,lM2,1)[0]
print(f"   power-fit slope d(logM)/d(log s2) = {p2:.4f}  (0=>log ; <0 => power loss)")
