# Exact check: does the per-step schurState codim accumulate (down a path) to Mval(M0,T)
# for an admissible T? And is the achiever T* reachable by a legal path?
# Adm/Mval transcribed EXACTLY from Foundations/Lambda.lean.
from itertools import product

def admBound(M, j, L):
    # j : Fin L, M : Fin(L+1). j.val=0 -> min(M0,M1), else M[j+1]
    if j == 0:
        return min(M[0], M[1])
    else:
        return M[j+1]

def tPrev(M, T, j):
    if j == 0:
        return M[0]
    else:
        return T[j-1]

def Mval(M, T):
    L = len(T)
    s = 0
    for j in range(L):
        s += (tPrev(M,T,j) - T[j]) * (M[j+1] - T[j])
    return s

def admPred(M, T, L):
    # T[j] <= admBound; weakly decreasing T[j] <= T[i] for i<=j; T[L-1]=0
    for j in range(L):
        if T[j] > admBound(M, j, L): return False
    for i in range(L):
        for j in range(L):
            if i <= j and T[j] > T[i]: return False
    if T[L-1] != 0: return False
    return True

def Adm(M):
    L = len(M)-1
    out = []
    ranges = [range(admBound(M,j,L)+1) for j in range(L)]
    for T in product(*ranges):
        if admPred(M, list(T), L):
            out.append(tuple(T))
    return out

def minAdm(M):
    A = Adm(M)
    return min(Mval(M,T) for T in A), A

# schurState: red = (M0-1, M1-1, M2, ...) at s.val<=1, requires M0,M1>=1. drop=2, ΣM drops by 2.
def schur_red(M):
    red = list(M)
    for s in range(len(M)):
        if s <= 1:
            red[s] = M[s]-1
    return tuple(red)

for M in [(2,2,2),(3,3,3),(3,2,3),(4,3,2),(2,3,2),(2,2,2,2),(3,3,3,3)]:
    m0, A = minAdm(M)
    achievers = [T for T in A if Mval(M,T)==m0]
    # Trace the schurState chain: M -> red -> red -> ... until a width hits the L=1 base or width<1 at pivot.
    chain = [M]
    cur = M
    steps_ok = True
    while True:
        L = len(cur)-1
        if L < 1: break
        # need M0>=1,M1>=1 to peel; if not, stop (degenerate / leaf)
        if cur[0] < 1 or cur[1] < 1:
            break
        nxt = schur_red(cur)
        # stop if no width drop possible / reached all-zero front
        if nxt == cur: break
        if sum(nxt) >= sum(cur):
            steps_ok = False; break
        chain.append(nxt)
        cur = nxt
        if sum(cur) <= 1: break
        if len(chain) > 20: break
    print(f"M={M}: minAdm={m0}, #achievers={len(achievers)} {achievers[:3]}")
    print(f"   schurState chain (drop=2/step): {chain}")
    print(f"   ΣM start={sum(M)}, chain widths={[sum(c) for c in chain]}")
