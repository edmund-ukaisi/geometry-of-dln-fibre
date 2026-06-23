# What makes the (0,j) ROW equality rankFn(cascade) 0 j = t*_j NON-VACUOUS?
# rankFn(cascade) 0 j = survivors(M_j, M_0, cascadeCount 0 j),
#   cascadeCount 0 j = min over s in 1..j of t*_s  (running MIN), t*=(M_0,T_0,...,T_{L-1}).
# survivors(M_j,M_0,x) = min(x, min(M_j,M_0)).
# So rankFn 0 j = min( min_{s<=j} t*_s , M_0 , M_j ).
# This = t*_j  REQUIRES:
#   (A) min_{1<=s<=j} t*_s = t*_j     <=> t* monotone-decreasing up to j (the running-min collapses to the endpoint)
#   (B) t*_j <= min(M_0, M_j)          <=> the survivors cap doesn't bite.
# If t* were NON-monotone, (A) fails and rankFn 0 j < t*_j -> the equality would be FALSE for that pattern
#   (the cascade can't realize a non-monotone running-rank profile). For ADMISSIBLE T, (A) always holds
#   (monotone, proven). So the (0,j) row equality is a THEOREM that USES monotonicity — the proof's real
#   content is showing (A) and (B) discharge. A witness that EXERCISES this needs:
#   - (A) to be non-trivial: there must be a j with a STRICT earlier drop then a plateau, OR a plateau then drop,
#     so the running-min "could" have been a strictly earlier (smaller) value if t weren't monotone --
#     i.e. >=2 DISTINCT nonzero running-rank levels among t*_1..t*_{L} (so the min is genuinely "selected").
#   - (B) to be non-trivial: there must be a j where t*_j is STRICTLY LESS than min(M_0,M_j) but EQUAL after
#     the survivors cap -- i.e. the cap min(M_0,M_j) > t*_j (so survivors actively returns t*_j not the cap),
#     AND ideally an increasing-width step M_{j-1}<M_j so M_j is NOT the binding width (tests survivors vs M_0/M_j).
#
# ANCHORS (2,2,2),(3,2,3): T*=(1,0). t*=(M_0,1,0). Running ranks: 2 distinct nonzero? t*_1=1 only -> just ONE
#   nonzero level (1). So (A) is vacuous: min over {1} or {1,0} trivially = endpoint, no "selection" among
#   >=2 distinct nonzero levels. THAT is the anchor coincidence: only one nonzero running-rank level.
def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
from itertools import product
def admPred(M,T):
    L=len(M)-1
    if any(T[j]>admBound(M,j) for j in range(L)): return False
    for i in range(L):
        for j in range(i,L):
            if T[j]>T[i]: return False
    if L>=1 and T[L-1]!=0: return False
    return True
def Adm(M):
    L=len(M)-1
    return [list(T) for T in product(*[range(admBound(M,j)+1) for j in range(L)]) if admPred(M,list(T))]
def tPrev(M,T,j): return M[0] if j==0 else T[j-1]
def Mval(M,T):
    L=len(M)-1; return sum((tPrev(M,T,j)-T[j])*(M[j+1]-T[j]) for j in range(L))
def achievers(M):
    adm=Adm(M); vals=[(T,Mval(M,T)) for T in adm]; mn=min(v for _,v in vals)
    return mn,[T for T,v in vals if v==mn]

def analyze(M,T,lab=""):
    L=len(M)-1; t=[M[0]]+list(T)
    # distinct nonzero running-rank levels among t_1..t_L
    distinct_nz = sorted(set(x for x in t[1:] if x>0), reverse=True)
    # (A) test: are there >=2 distinct nonzero levels? -> running-min genuinely selects
    A = len(distinct_nz)>=2
    # (B) test: is there a j with t_j strictly < min(M_0,M_j) (cap doesn't bite, survivors returns t_j)?
    Bjs=[j for j in range(1,L+1) if t[j] < min(M[0],M[j]) and t[j]>0]
    # increasing-width step
    incr=[s for s in range(L) if M[s]<M[s+1]]
    print(f"  {lab} M={M} T*={T}: t*={t}")
    print(f"     distinct nonzero running-rank levels = {distinct_nz}  (>=2 distinct => (A) non-trivial: {A})")
    print(f"     (B) j with t_j < min(M_0,M_j), t_j>0 (cap-non-binding): {Bjs}")
    print(f"     increasing-width steps M_s<M_s+1: {incr}")
    print(f"     ==> EXERCISES both (A)+(B)+(incr): {A and len(Bjs)>0 and len(incr)>0}")

print("ANCHORS (vacuity-prone):")
for M in [[2,2,2],[3,2,3]]:
    mn,ach=achievers(M); analyze(M,ach[0],"anchor")
print()
print("WITNESS CANDIDATES (L>=3):")
for M in [[2,3,4,3],[3,4,5,4],[3,4,4,3],[2,3,3,2],[3,3,3,3]]:
    mn,ach=achievers(M)
    for T in ach:
        analyze(M,T,"cand")
    print()
