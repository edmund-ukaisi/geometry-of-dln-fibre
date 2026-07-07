from functools import lru_cache
import random

@lru_cache(maxsize=None)
def minAdmRec(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

# SHIFTED peel (the design): thr = (1/2)minAdm
@lru_cache(maxsize=None)
def thr_shift(M):
    L=len(M)-1
    if L==0: return 0.0
    if L==1: return M[0]*M[1]/2.0
    return min((M[0]-t)*(M[1]-t)/2.0 + thr_shift((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

# EXPONENT-PRESERVING peel (banked fibre_lintegral_mul_le): peel one factor off X·Y,
# cap c' < p/2 (row count of the peeled factor), SAME c' on residual Y.
# Both-sided (transpose symmetry), leaves = free-matrix (single factor) base c'<rows*cols/2... 
# but the residual keeps SAME c', so total reach = the MINIMUM cap along the peel = min_s M_s/2
# with square-first-factor SchurCore reach at 2-factor leaves.
@lru_cache(maxsize=None)
def reach_preserving(M):
    L=len(M)-1
    if L==1:
        return M[0]*M[1]/2.0                       # single free matrix: c' < rows*cols/2
    if L==2:
        # SchurCore reach (square-first-factor) = (1/2)minAdm when M0==M1, else best peel
        # exponent-preserving 2-matrix reach = min over: peel-front cap M0/2 + SAME c' tail,
        # peel-back cap M2/2, or (if M0==M1) the closed square-Schur = (1/2)minAdm.
        opts=[min(M[0]/2.0, reach_preserving((M[0],M[1]))),      # peel front A0 (p=M0), tail (M1,M2) same c'
              min(M[2]/2.0, reach_preserving((M[1],M[2])))]      # peel back  (transpose)
        if M[0]==M[1]:
            opts.append(minAdmRec(M)/2.0)                        # square SchurCore closed
        if M[1]==M[2]:
            opts.append(minAdmRec(M)/2.0)
        return max(opts)
    # L>=3: peel one end factor, SAME exponent on the (product) residual -> min(cap, tail reach at same c')
    front = min(M[0]/2.0, reach_preserving(M[1:]))               # peel A0, cap M0/2, tail same c'
    back  = min(M[-1]/2.0, reach_preserving(M[:-1]))             # peel last, cap ML/2
    return max(front, back)

print("=== SHIFTED peel (design) vs EXPONENT-PRESERVING peel (banked fibre engine) ===")
print(f"{'M':16} | {'(1/2)minAdm':>11} | {'shifted (design)':>16} | {'preserving (banked)':>19} | undershoot")
print("-"*95)
for M in [(2,2,2),(2,2,2,2),(3,3,3,3),(4,4,2,2),(2,2,2,3),(2,3,4),(4,4,4,4)]:
    tgt=minAdmRec(M)/2.0; sh=thr_shift(M); pr=reach_preserving(M)
    fac = tgt/pr if pr>0 else float('inf')
    print(f"{M!s:16} | {tgt:11.2f} | {sh:16.2f} | {pr:19.2f} | {fac:.2f}x")
print("""
=> The SHIFTED peel reaches (1/2)minAdm on EVERY chain incl. the (3,3,3,3) staircase
   the exponent-preserving engine undershoots by 2x.  The shift IS the missing mechanism.
""")

# ---- Numeric integrability GUIDE (not load-bearing): does the box integral of ||AB||^{-2c'}
#      for (2,2,2) show the divergence onset at c'=3/2 ? crude MC of E[||AB||^{-2c'}] over box. ----
import numpy as np
def mc_moment(widths, cprime, n=4_000_000, seed=0):
    rng=np.random.default_rng(seed)
    L=len(widths)-1
    mats=[rng.uniform(-1,1,size=(n,widths[s],widths[s+1])) for s in range(L)]
    P=mats[0]
    for s in range(1,L): P=np.matmul(P,mats[s])
    fro2=(P**2).sum(axis=(1,2))
    fro2=np.maximum(fro2,1e-300)
    vals=fro2**(-cprime)
    return vals.mean(), np.median(vals)

print("Numeric GUIDE (MC mean of ||AB||^{-2c'} over box, (2,2,2)); finite integral <-> stable mean:")
for cp in [1.0, 1.3, 1.45, 1.55, 1.7, 2.0]:
    m,med=mc_moment((2,2,2),cp,n=3_000_000)
    print(f"   c'={cp:.2f} (target 3/2=1.5): MC-mean={m:.3e}  median={med:.3e}")
