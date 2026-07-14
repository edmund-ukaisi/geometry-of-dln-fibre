"""
Addendum to m2gtm1_scope.py.
(A) HONEST per-regime floor (matches the S1 cert): L=0 -> Z_deep = I_{M2} is a KNOWN
    full-rank constant, honest floor = M2 (no shell needed); L>=1 -> variable Z_deep,
    shell-certified floor m = min(M1,ML)-j.  Report the genuine residual.
(B) REVERSE-PEEL test: can peeling from the BACK (a reversal, which IS implementable as
    "front-peel of the reversed chain") avoid the divergent pattern that front-peel hits?
(C) Deep-bottleneck check restated under the honest floor.
"""
from functools import lru_cache
from itertools import product

@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(M)
    if len(M) == 1: return 0
    if len(M) == 2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t) + minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

def binding_cuts(M):
    mA = minAdm(M)
    return [t for t in range(min(M[0],M[1])+1)
            if (M[0]-t)*(M[1]-t)+minAdm((t,)+tuple(M[2:]))==mA]

def honest_fail_shells(M):
    """proper off-sector shells failing the HONEST-floor convergence (front-peel of M)."""
    out=[]
    L0 = (len(M)==3)
    ML=M[-1]; M1=M[1]; M2=M[2]; deepbott=min(M[2:])
    for tstar in binding_cuts(M):
        r=min(M[0]-tstar, M[1]-tstar)
        for j in range(1,r+1):
            u=tstar+j; a=M[0]-u; b=M1-u
            if a<1 or b<1: continue
            floor = M2 if L0 else (min(M1,ML)-j)   # honest per-regime floor
            if floor < a+b:
                out.append(dict(M=M,u=u,a=a,b=b,floor=floor,deepbott=deepbott,
                                true_conv=(deepbott>=a+b)))
    return out

# ---- (A) honest residual over 3..5-width, widths 2..5 ------------------------
front_fail=[]
for Llen in [3,4,5]:
    for M in product(range(2,6),repeat=Llen):
        front_fail += honest_fail_shells(M)
print("HONEST-floor front-peel failing shells (3..5 widths):", len(front_fail))
print("  all are L>=1 (no genuine L=0 residual)?", all(len(r['M'])>=4 for r in front_fail))
print("  all are M2>M1?", all(r['M'][2]>r['M'][1] for r in front_fail))
print("  all have deep-bottleneck >= a+b (finer-strat generic stratum converges)?",
      all(r['true_conv'] for r in front_fail))
# restrict to the cert's L>=1 [2..5]^{4,5} range for the 7/64 cross-check
lge1=[r for r in front_fail if len(r['M']) in (4,5)]
print("  L>=1 (4,5-width) honest failing shells:", len(lge1))

# ---- (B) reverse-peel: does the reversed chain avoid ALL honest failures? ----
distinctM = sorted(set(r['M'] for r in front_fail))
rev_still=0; rev_ok=0
for M in distinctM:
    R=tuple(reversed(M))
    if honest_fail_shells(R):
        rev_still+=1
    else:
        rev_ok+=1
print("\n[reverse-peel] distinct front-failing chains:", len(distinctM))
print("  reversed chain ALSO honest-fails (front-peel of reverse):", rev_still)
print("  reversed chain has NO honest failure (reversal would cover it):", rev_ok)
# a chain covered by NEITHER end:
neither=[M for M in distinctM if honest_fail_shells(tuple(reversed(M)))]
print("  => reversal-alone covers", rev_ok, "of", len(distinctM),
      "; NOT covered by either end:", len(neither))
if neither[:8]:
    print("     examples needing more than an end-choice:", neither[:8])
