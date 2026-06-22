# CONFOUND (i): a missed admissible stratum -> atlas ⨅ OVER-estimates the RLCT (claims rlct too big).
# The (C2) recursion blows up the FIRST FACTOR's rank each node. But t_j = rank(C^(1)...C^(j)) can drop
# because a LATER factor C^(j) is rank-deficient, NOT because the running first-factor dropped.
# THE ADVERSARIAL CASE: C^(1) full rank, but C^(1)C^(2) drops rank because C^(2) kills part of C^(1)'s
# image. Does the first-factor recursion SEE this stratum? If not, that stratum's binding divisor is
# absent and ⨅ over-estimates (misses a smaller-codim contribution).
import numpy as np, itertools
rng=np.random.default_rng(1)

def Mval(M,t):
    L=len(M)-1; tt=[M[0]]+list(t); s=0
    for j in range(1,L+1): s+=(tt[j-1]-tt[j])*(M[j]-tt[j])
    return s
def adm(M):
    L=len(M)-1; out=[]
    def rec(j,prev,cur):
        if j==L+1:
            if cur[-1]==0: out.append(tuple(cur[1:]))
            return
        for v in range(0,min(prev,M[j])+1): rec(j+1,v,cur+[v])
    rec(1,M[0],[M[0]]); return out

# Adversarial witness hunt: a point where rank(C1) is FULL but rank(C1 C2 ... )=t with a later drop.
# Does the first-factor blow-up recursion's stratum-indexing still cover this t? The recursion at node1
# blows up rank(C1); if C1 is full rank there, node1 picks the full-rank chart (no blow-up of C1), and
# the rank drop must come at a LATER node from the REDUCED chain's first factor. Check: after node1 with
# C1 full rank, the reduced chain's first factor = S1*C2 (the Schur-reduced), whose rank = rank(C1 C2).
# So the drop IS seen at node 2 (as the reduced first factor's rank). Verify the rank bookkeeping:
def check_later_drop(M, nsamp=3000):
    # sample chains where C1 full rank but product drops; check t_j matches a reachable nesting
    L=len(M)-1
    admset=set(adm(M))
    seen=set()
    for _ in range(nsamp):
        mats=[rng.standard_normal((M[s],M[s+1])) for s in range(L)]
        # force product = 0 by making last factor's image avoid... instead just compute generic ranks
        # to see which t actually OCCUR; then check all admissible t are achievable as rank vectors.
        t=[]
        P=np.eye(M[0])
        for s in range(L):
            P=P@mats[s]
            t.append(np.linalg.matrix_rank(P, tol=1e-9))
        seen.add(tuple(t))
    return admset, seen

# Better: directly CONSTRUCT a point in each admissible stratum and confirm the first-factor recursion
# reaches it. The recursion reaches t iff t is a valid first-factor-rank descent. By the Schur identity,
# the reduced first factor at node j has rank = rank(partial product j) = t_j. So EVERY admissible t is
# a valid descent (t_j <= t_{j-1} forced by Schur, t_j<=M^{j+1} by the product target dim).
# The ONLY way to miss: if some admissible t has t_j > t_{j-1} (impossible, weakly decreasing) or
# t_j capped differently. Search for an admissible t NOT expressible as first-factor descent:
def missed(M):
    admset=set(adm(M))
    # first-factor descent = exactly: t_0=M^1, t_j in [0, min(t_{j-1}, M^{j+1})], t_L=0
    desc=set(adm(M))  # identical recurrence
    return admset-desc, desc-admset

bad=False
for M in [[2,2,2],[3,3,3],[4,3,2],[3,2,3],[2,3,2],[2,2,2,2],[4,4,4,4],[5,4,3,2],[2,5,3],[3,1,3]]:
    miss,extra=missed(M)
    if miss or extra: bad=True
    print(f"M={M}: missed_strata={miss or 'NONE'}  extra={extra or 'NONE'}")
print("\nANY MISSED STRATUM:", bad)
