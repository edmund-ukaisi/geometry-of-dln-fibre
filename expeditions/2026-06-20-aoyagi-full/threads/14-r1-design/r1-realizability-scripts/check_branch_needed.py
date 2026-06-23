from itertools import product
def admBound(M, j): return min(M[0], M[1]) if j == 0 else M[j+1]
def tPrev(M, T, j): return M[0] if j == 0 else T[j-1]
def Mval(M, T): return sum((tPrev(M,T,j)-T[j])*(M[j+1]-T[j]) for j in range(len(T)))
def admPred(M, T):
    L=len(T)
    if any(T[j]>admBound(M,j) for j in range(L)): return False
    if any(i<=j and T[j]>T[i] for i in range(L) for j in range(L)): return False
    return T[L-1]==0
def Adm(M):
    L=len(M)-1
    return [tuple(T) for T in product(*[range(admBound(M,j)+1) for j in range(L)]) if admPred(M,list(T))]
def minAdm(M): A=Adm(M); return min(Mval(M,T) for T in A), A

# QUESTION: does the achiever-only route need BRANCHING, or can ONE schurState chain carry the achiever?
# The achiever leaf must have codim-list CONTAINING minAdm. A single chain's codim list = the per-step
# blow-up codims. If the uniform schurState step has a FIXED codim (e.g. always Mval of the *front-collapse*
# stratum), the single chain may MISS the achiever stratum's codim.
# Concretely: (4,3,2) achievers are (2,0),(3,0) [minAdm=6], but the front-collapse chain corresponds to
# the all-front-drop profile. Check: which stratum does the uniform "drop both front widths" correspond to?
# schurState drops M0,M1 by 1 -> after k steps, front widths are M0-k, M1-k. The "T" that this realizes
# (the rank profile pinned) — the deepest reachable T from collapsing front. Compare to achiever.
# The pp2 g207/g214 concern: minAdm(schurState M) < minAdm(M0) — the reduced chain's OWN minAdm undershoots
# the root's. Verify this undershoot (the reason for root-anchoring PivotWitness at M0):
for M in [(2,2,2),(3,3,3),(4,3,2),(3,3,3,3),(5,4,3,2)]:
    m0_root,_ = minAdm(M)
    # schurState reduced chain:
    red = tuple((M[s]-1 if s<=1 else M[s]) for s in range(len(M)))
    if red[0]>=0 and red[1]>=0 and min(red)>=0 and red[0]<=red[1]+99:
        try:
            m0_red,_ = minAdm(red)
        except Exception as e:
            m0_red = None
    print(f"M={M}: minAdm(M0)={m0_root}; schurState.red={red}, minAdm(red)={m0_red}  -> undershoot={m0_red is not None and m0_red < m0_root}")
