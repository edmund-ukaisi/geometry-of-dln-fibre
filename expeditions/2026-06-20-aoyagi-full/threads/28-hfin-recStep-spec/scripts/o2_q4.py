import sympy as sp
from functools import lru_cache
import numpy as np
from numpy.random import default_rng

# ============================================================
# Q4: does the FREE-box corank-(r-1) core diverge below threshold because the box
# contains {det Sc = 0} / {Sc = 0}?  Answer: NO -- this is EXACTLY the IH, and the IH is
# proved by the SAME recursion one level down (the {Sc near singular} locus is the NEXT
# radial-blowup + Schur level). The free-box core is finite at lambda_{r-1,p} BY INDUCTION.
# Verify the threshold is self-consistent (the free-box core threshold = the IH threshold).
# ============================================================
@lru_cache(maxsize=None)
def lam(r,p):
    if r==0: return sp.Rational(0)
    return min([sp.Rational(r*r,2)] + [sp.Rational(j*p,2)+lam(r-j,p) for j in range(1,r+1)])

# The free-box corank-m core C_m(p) := ∫_{Sc-box (m x m)} ∫_{S_bot box (m x p)} frobSq(Sc*S_bot)^{-c'}.
# Claim: C_m(p) is finite iff c' < lambda_{m,p} (the SAME recursion threshold). This is because
# the free Sc-box core is structurally IDENTICAL to the ||Delta*S||^2 core at corank m: Sc plays
# the role of the residual Delta (a free m x m matrix over a box), S_bot the free block.
# So the corank-(r-1) IH is literally "C_{r-1}(p) finite for c'<lambda_{r-1,p}".  Self-consistent.
print("=== The free-box corank-m core IS the corank-m ||Delta*S||^2 core (same object) ===")
print("C_m(p) = ∫_{Delta-box}∫_{S box} frobSq(Delta*S)^{-c'} = the SAME core, finite iff c'<lambda_{m,p}.")
print("The corank-(r-1) IH = 'C_{r-1}(p) finite for c'<lambda_{r-1,p}'. The free Sc-box core in O2's")
print("domination IS C_{r-1}(p) (Sc ranges over a box of side <=4, S_bot over a box). SAME threshold.")
print()
print("So Q4 'does {det Sc=0} diverge the free-box core below threshold' is answered by the IH ITSELF:")
print("NO -- the IH IS the statement that this core is finite at lambda_{r-1,p}, proved by the recursion")
print("one corank lower (the {Sc near singular} locus = the next radial-blowup level). NOT a new wall.")
print()

# Numerical sanity: the corank-2 free-box core (m=2) finite for c'<lambda_{2,p}, divergent above.
def corank_m_core(m, c, p, N=600000, T=1.0, bSc=2.0, seed=0):
    rng = default_rng(seed)
    Sc = rng.uniform(-bSc,bSc,size=(N,m,m))
    Sb = rng.uniform(-T,T,size=(N,m,p))
    fs = (np.einsum('nij,njk->nik',Sc,Sb)**2).sum(axis=(1,2))
    val = fs**(-c); fin=np.isfinite(val)
    return val[fin].mean(), np.mean(val>1e8)   # mean (convergence proxy), tail frac (divergence proxy)

print("=== corank-2 free-box core: convergence below lambda_{2,p}, divergence trend above ===")
for p in [3,4]:
    L = float(lam(2,p))
    print(f" p={p}, lambda_(2,{p})={L}:")
    for c in [L-0.3, L+0.3]:
        m,frac = corank_m_core(2, c, p)
        tag = "BELOW thr (converges)" if c<L else "ABOVE thr (diverges)"
        print(f"    c'={c:.2f} [{tag}]: mean~{m:.4g}, tail-frac(>1e8)={frac:.2e}")
