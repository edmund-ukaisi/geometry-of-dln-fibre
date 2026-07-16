import numpy as np
rng=np.random.default_rng(7)
# Faithful-ish edge model: a=b=2, rho=3. Keep Γ on BOX, integrate over A_cor box AND C box.
# freedSchurLoss ~ w + frobSq(C0 + Γ·K),  K=A_cor·Z (rank<=rho),  C0 = C (a×n) over box.
# Test: does ∫_{C,A_cor,Γ box}(w+frobSq(C0+ΓK))^{-c'} converge at edge, and its w-scaling.
a,b,rho,n=2,2,3,3
Z=np.eye(3)
def full_box(w,c,NC=1500,NA=1500,NG=1200):
    tot=0.0
    for _ in range(NC):
        C0=rng.uniform(-1,1,size=(a,n))
        A=rng.uniform(-1,1,size=(b,rho)); K=A@Z
        G=rng.uniform(-1,1,size=(NG,a,b))
        E=C0[None]+np.einsum('gij,jk->gik',G,K)
        loss=w+np.sum(E*E,axis=(1,2))
        tot+= (2.0**(a*b))*np.mean(loss**(-c))          # Γ-box integral
    volC=2.0**(a*n); volA=2.0**(b*rho)
    return volC*volA*tot/NC
c=2.4  # ab/2=2, target reduction exponent c-ab/2=0.4
ws=[0.4,0.1,0.025,0.00625,0.0015625]
print(f"EDGE a=b=2 rho=3 c'={c} ab/2=2 ; FULL box (Γ,A_cor,C all boxed).  target I~w^-(c'-ab/2)=w^-0.4")
vs=[full_box(w,c) for w in ws]
for w,v in zip(ws,vs): print(f"  w={w:.6f}  I={v:11.2f}")
for i in range(len(ws)-1):
    p=np.log(vs[i+1]/vs[i])/np.log(ws[i+1]/ws[i]); print(f"    local exponent p (I~w^p): {p:.3f}")
print("\n  If p -> -0.4 (=-(c'-ab/2)) with a mild log slope, edge reduces cleanly by ab/2 (per-exponent).")
print("  If p -> -2.4 (=-c'), NO reduction (bad).  If p -> 0, over-resolved (finite, no w-sing).")
