"""
Two discriminators for the d<=1 native arm:
(1) Does the a=0 WIDE (b>=1) front rank-sector reach minAdm with the NAIVE single-factor front codim
    (M0-s)(M1-s) [=> native decoration], or does the joint product-corank C_s undershoot [=> cite wall]?
    Codex's C_s (fixed rank X = s): C_s = (m-s)(n-s) + (s-r)(k-r), m=M0,n=M1,k=M2. But on outerDom P is
    INVERTIBLE so rank X = m ALWAYS (no s<m tube). Check: is min over the ACHIEVABLE strata (single-factor,
    rank drop from Y only, codim (M0-s)(M1-s) via the deepened cut) == minAdm?  [d1_charge already: 0/5292]
    Here additionally test Codex's C_s min vs naive to see if a s<m tube (if it existed) would undershoot.
(2) Shallow (u=t<=2, plausibly plain-hIH via shell+Hoelder) vs deep (u>=3, needs decoration) census
    across ALL d<=1 cuts.
"""
from functools import lru_cache
from itertools import product

@lru_cache(maxsize=None)
def minAdmRec(M):
    n = len(M)
    if n <= 1: return 0
    if n == 2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t) + minAdmRec((t,)+M[2:])
               for t in range(0, min(M[0],M[1])+1))
def redChain(t, M): return (t,)+M[2:]
def peelCharge(M,u): return (M[0]-u)*(M[1]-u)
def gen_chains(arities, wmax):
    for L in arities:
        for M in product(range(1, wmax+1), repeat=L):
            yield M

# (1) Codex C_s discriminator for a=0 cuts (m=M0,n=M1,k=M2). rank drop r of W in 0..min(m,k).
#     naive codim (single factor, X full rank): d_naive(r) = (m-r)(k-r) . (the {rank W=r} codim when X surjective)
#     joint (allowing rank X = s): C_s(r) = min_s>=r (m-s)(n-s) + (s-r)(k-r).
#     If for some r, min_s C_s(r) < d_naive(r), a hidden joint incidence EXISTS (would undershoot).
hidden_joint = 0; a0_checked = 0
for M in gen_chains([4,5],6):
    m,n,k = M[0],M[1],M[2]
    if m < n:  # a=0 wide (M0<M1, b>=1)
        a0_checked += 1
        for r in range(0, min(m,k)+1):
            d_naive = (m-r)*(k-r)
            Cs = min((m-s)*(n-s) + (s-r)*(k-r) for s in range(r, m+1))
            if Cs < d_naive:
                hidden_joint += 1
                break
print("(1) a=0 WIDE cuts checked:", a0_checked, " with a hidden-joint undershoot (Cs<naive):", hidden_joint)

# But note: P invertible => rank X = m always => only s=m achievable => C_m = (m-r)(k-r) = naive. Confirm s=m term:
print("    [P-invertible forces s=m; C_m == naive by construction, so achievable strata never undershoot]")

# (2) shallow vs deep census over d<=1 cuts (u=t). Also split by sub-case.
cats = {}
for M in gen_chains([4,5],6):
    M0,M1 = M[0],M[1]
    for t in range(1, min(M0,M1)+1):
        a=M0-t; b=M1-t; d=min(a,b); u=t
        if d>1: continue
        if d==0 and a==0 and b>0: sub='d0_a0_wide'
        elif d==0 and b==0 and a>0: sub='d0_b0_tall'
        elif d==0 and a==0 and b==0: sub='d0_square'
        elif d==1 and a<u: sub='d1_aLTu'
        else: sub='d1_aGEu'
        depth = 'shallow(u<=2)' if u<=2 else 'deep(u>=3)'
        cats[(sub,depth)] = cats.get((sub,depth),0)+1
print("(2) d<=1 cut census by sub-case x depth:")
for sub in ['d0_a0_wide','d0_b0_tall','d0_square','d1_aLTu','d1_aGEu']:
    sh = cats.get((sub,'shallow(u<=2)'),0); dp = cats.get((sub,'deep(u>=3)'),0)
    print(f"   {sub:14s}  shallow(u<=2)={sh:5d}   deep(u>=3)={dp:5d}")
