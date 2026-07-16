import numpy as np
rng=np.random.default_rng(11)
Zf=rng.standard_normal((3,3))
# WORST case Ccross=0: H(w)=int_Acor int_Gamma (w+frobSq(Gamma A_cor Zf))^{-c'}.
# Claim: dominant {Gamma=0} component (codim ab=4) gives H ~ w^{-(c'-2)} * ln(1/w) (front-charge log
# becomes a LOG CORRECTION, not a divergence). reduction = ab/2 = 2 exactly.
def H0(w,cp,N=4_000_000):
    A=rng.uniform(-1,1,(N,2,3)); G=rng.uniform(-1,1,(N,2,2))
    M=np.einsum('nij,jk->nik',A,Zf); GM=np.einsum('nij,njk->nik',G,M)
    base=w+np.sum(GM**2,(1,2))
    return (2.0**10)*np.mean(base**(-cp))
print("Ccross=0 (worst case): test H(w) ~ w^{-(c'-2)} * ln(1/w)  [reduction ab/2=2 + LOG]")
for cp in [3.0,3.5,4.0]:
    ws=np.array([2.0**(-k) for k in range(3,13)])
    Hs=np.array([H0(w,cp) for w in ws])
    # plain power fit
    beta=-np.polyfit(np.log(ws),np.log(Hs),1)[0]
    # test log-corrected: H*w^{c'-2} should ~ A + B*ln(1/w)  (linear in ln(1/w))
    y=Hs*ws**(cp-2.0); x=np.log(1/ws)
    slope,icpt=np.polyfit(x,y,1)
    print(f" c'={cp}: plain beta={beta:.3f} (vs c'-2={cp-2.0}).  "
          f"H*w^(c'-2) vs ln(1/w): slope={slope:.3g} icpt={icpt:.3g} "
          f"(slope>0 & ~linear => LOG correction confirmed)")
    print(f"     H*w^(c'-2) values:", "  ".join(f"{v:.3g}" for v in y[::2]))
