"""(D) corank-one matrix->scalar localization (care-point). Verifies: near rank(Q_b)=b-1, the corank
energy E=frobSq(C·Q̃ₚ + Γ·Q_b) has fragile (w-direction) component = C·v + σ·(Γη) EXACTLY, where
σ=σ_min(Q_b), η/w = fragile left/right singular vectors, v=Q̃ₚ·w. So the local model is
(w_shift + ||C·v + σ·Γη||²)^(−c'); C=0 => (σ·Γη)² = edgebrick's log model."""
import numpy as np
rng=np.random.default_rng(0)
def check(a,b,n,u,N=200000):
    worst=0.0
    for _ in range(N//200):
        U=np.linalg.qr(rng.standard_normal((b,b)))[0]; Vt=np.linalg.qr(rng.standard_normal((n,n)))[0][:b]
        sv=np.abs(rng.standard_normal(b))+0.3; sigma=rng.uniform(0,0.05); sv[-1]=sigma
        Qb=(U*sv)@Vt; eta=U[:,-1]; w=Vt[-1]
        Qtp=rng.standard_normal((u,n)); C=rng.uniform(-1,1,(a,u)); Gam=rng.uniform(-1,1,(a,b))
        v=Qtp@w; frag=C@v+sigma*(Gam@eta); w_comp=(C@Qtp+Gam@Qb)@w
        worst=max(worst,np.max(np.abs(w_comp-frag)))
    return worst
for (a,b,n,u) in [(1,1,3,2),(2,1,3,2),(1,2,4,3),(2,2,4,3),(3,1,4,2)]:
    print(f"a={a} b={b} n={n} u={u}: max|w_comp(E) − (C·v+σ·Γη)| = {check(a,b,n,u):.2e}")
