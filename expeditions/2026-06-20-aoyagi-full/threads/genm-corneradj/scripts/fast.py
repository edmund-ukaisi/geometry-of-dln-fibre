import numpy as np
rng=np.random.default_rng(7)
Zf=rng.standard_normal((3,3))
def H(w,cp,Cs,N=1_500_000):
    A=rng.uniform(-1,1,(N,2,3)); G=rng.uniform(-1,1,(N,2,2))
    M=np.einsum('nij,jk->nik',A,Zf); GM=np.einsum('nij,njk->nik',G,M)
    Cc=Cs*rng.standard_normal((2,3))
    base=w+np.sum((Cc[None]+GM)**2,(1,2))
    return (2.0**10)*np.mean(base**(-cp))
print("PART2 honest H(w)~w^-beta, need beta<3.5 for full-obj conv at c'=4.49:")
for Cs in [1.0,0.1,0.0]:
    ws=np.array([2.0**(-k) for k in range(11)])
    for cp in [4.49]:
        Hs=np.array([H(w,cp,Cs) for w in ws])
        beta=-np.polyfit(np.log(ws[5:]),np.log(Hs[5:]),1)[0]
        print(f"  Ccross-scale={Cs}: c'={cp} beta={beta:.3f} red={cp-beta:.2f} -> {'CONV(beta<3.5)' if beta<3.5 else 'RISK'}  Htail={Hs[-1]:.3g}")
