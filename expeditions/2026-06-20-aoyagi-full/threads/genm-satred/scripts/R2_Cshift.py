"""(D) R2 (C-shift) EXACT form. G(W,v,β,c') = ∫_{C∈[-1,1]^{a×u}} (W+‖(of C).mulVec v + β‖²)^{-c'} dC.
Verified: (i) β-INVARIANT as a bound (shift absorbed — the C-integration's whole point); (ii) W-power
a/2−c' for c'>a/2, LOG(1/W) at c'=a/2 (=ab/2 for b=1, the corank-one tie) — the log lives in the a-dim
RADIAL, not a σ-coupling; (iii) G ∝ ‖v‖^{-a} (the C·v density sup). So
   G ≤ ‖ρ_v‖∞ · R_a(W,c'),   ‖ρ_v‖∞ ≤ (2‖v‖_∞)^{-a},   R_a(W,c') = ∫_{ball_a}(W+‖ζ‖²)^{-c'}dζ
   = C_a·W^{a/2−c'} (c'>a/2)  /  ≍ log(1/W) (c'=a/2).  R_a is scaledRadialEuclid/JapaneseBracket (P3)."""
import numpy as np
def G_a1(W,v,beta,cp,N=4_000_000):
    u=len(v); C=np.random.uniform(-1,1,(N,u)); return ((W+(C@v+beta)**2)**(-cp)).mean()*(2**u)
v=np.array([0.7,0.4])
print("β-invariance (bound) + W-power (a=1, a/2=0.5):")
for cp in [0.8,0.5]:
    for W in [1e-2,1e-4,1e-6]:
        g0,gb=G_a1(W,v,0.0,cp),G_a1(W,v,0.3,cp); ref=W**(0.5-cp) if cp>0.5 else np.log(1/W)
        print(f"  c'={cp} W={W:.0e}: G(0)={g0:.3g} G(.3)={gb:.3g} (β-inv) / ref={ref:.3g} → G/ref={g0/ref:.2f}")
print("v-scaling G∝‖v‖^{-1} (a=1): ", end="")
for vs in [1.0,0.5,0.25]:
    print(f"‖v‖={vs}:G·‖v‖={G_a1(1e-4,np.array([vs,0.]),0.,0.8)*vs:.1f} ", end="")
print("(const)")
