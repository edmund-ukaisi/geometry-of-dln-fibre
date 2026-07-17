"""
b=0 tall/square Wishart census + a>=u multi-level recursion reach.
minAdmRec transcribed from RouteMLayerSplit.lean.
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

def gen_chains(arities, wmax):
    for L in arities:
        for M in product(range(1, wmax+1), repeat=L):
            yield M

# b=0 wing (M1<=M0, t=M1, a=M0-M1, corank empty). Front tall [P;C] M0 x M1, FREE box.
# Wishart det(P^T P + C^T C)^{-M2/2} = qbox (qbox-b,qbox-q,alpha)=(M1,M0,M2): conv iff M2 <= a = M0-M1.
b0_oneshot = 0; b0_recurse = 0; b0_total = 0
sq_oneshot = 0; sq_recurse = 0; sq_total = 0   # square M0==M1 subset
for M in gen_chains([4,5], 6):
    n = len(M); M0,M1,M2 = M[0],M[1],M[2]
    if M1 <= M0:  # b=0 wing at t=M1
        a = M0 - M1
        b0_total += 1
        # one-shot qbox: converges iff M2 <= a  (i.e. M2 < a+1)
        if M2 <= a: b0_oneshot += 1
        else: b0_recurse += 1
        if M0 == M1:
            sq_total += 1
            if M2 <= a: sq_oneshot += 1   # a=0 here, so M2<=0 never -> always recurse
            else: sq_recurse += 1

print("b=0 wing (t=M1): total", b0_total, "one-shot qbox (M2<=a):", b0_oneshot, "recurse (M2>a):", b0_recurse)
print("  square subset (M0==M1, a=0):", sq_total, "one-shot", sq_oneshot, "recurse", sq_recurse)

# ---- a>=u d=1: does the reduced-chain RECURSION reach minAdm even when one-shot qbox fails? ----
# The claim: the pivot-Gram charge folds into redChain t M's own recursion. Check the ARITHMETIC surrogate:
# is there a sub-cut t' of redChain t M s.t. the marginal q becomes strict? Concretely check the
# min-over-strata identity holds for the corank rank-sector at a>=u d=1 cuts too:
#   for d=1 b=1 cut t, corank rank r in {0,1}; strata reduce to redChain (t+ (b-r)) M = redChain (t+1-r) M.
#   min_{r in 0..1}[ peelCharge(t+1-r) + minAdm(redChain (t+1-r) M) ] should be >= minAdm(M).
def peelCharge(M,u): return (M[0]-u)*(M[1]-u)
d1_strata_fail = 0; d1_strata_total = 0
for M in gen_chains([4,5], 6):
    M0,M1 = M[0],M[1]; mA = minAdmRec(M)
    for t in range(1, min(M0,M1)+1):
        a=M0-t; b=M1-t; d=min(a,b); u=t
        if d==1:
            # corank block a x b, min(a,b)=1. rank drop strata; deepened cuts u' in [t, min(M0,M1)]
            vals = [ peelCharge(M,up) + minAdmRec(redChain(up,M)) for up in range(t, min(M0,M1)+1) ]
            d1_strata_total += 1
            if min(vals) < mA: d1_strata_fail += 1
print("d=1 corank rank-sector min>=minAdm fails:", d1_strata_fail, "/", d1_strata_total)
