import itertools
from functools import lru_cache

# ---- Faithful minAdm from the Lean defs (Lambda.lean) ----
# Mval(M,T) = sum_{j=0}^{L-1} (tPrev_j - T_j)(M_{j+1} - T_j),  tPrev_0 = M_0, tPrev_j = T_{j-1}
# admPred: T_j <= admBound_j (admBound_0=min(M0,M1), else M_{j+1}); weak-decrease T_i>=T_j for i<=j; T_{L-1}=0
# minAdm = min over Adm of Mval

def Mval(M, T):
    L = len(T)
    s = 0
    for j in range(L):
        tprev = M[0] if j == 0 else T[j-1]
        s += (tprev - T[j]) * (M[j+1] - T[j])
    return s

def admBound(M, j):
    return min(M[0], M[1]) if j == 0 else M[j+1]

def is_adm(M, T):
    L = len(T)
    for j in range(L):
        if T[j] > admBound(M, j): return False
    for i in range(L):
        for j in range(L):
            if i <= j and T[j] > T[i]: return False
    if L >= 1 and T[L-1] != 0: return False
    return True

def adm_cone(M):
    L = len(M) - 1
    ranges = [range(admBound(M, j)+1) for j in range(L)]
    return [T for T in itertools.product(*ranges) if is_adm(M, T)]

def minAdm_brute(M):
    cone = adm_cone(M)
    return min(Mval(M, T) for T in cone), cone

# ---- minAdmRec (RouteMLayerSplit.lean) ----
@lru_cache(maxsize=None)
def minAdmRec(M):
    L = len(M) - 1
    if L == 0:
        return 0
    if L == 1:
        return M[0]*M[1]
    # L >= 2: min over t in 0..min(M0,M1) of (M0-t)(M1-t) + minAdmRec(redChain t M)
    # redChain t M = (t, M_2, ..., M_L)  (front two widths collapsed to t)
    best = None
    for t in range(min(M[0], M[1])+1):
        red = (t,) + M[2:]
        v = (M[0]-t)*(M[1]-t) + minAdmRec(red)
        best = v if best is None else min(best, v)
    return best

def binding_paths(M):
    """All admissible T achieving minAdm, with per-boundary decomposition."""
    mval, cone = minAdm_brute(M)
    out = []
    for T in cone:
        if Mval(M, T) == mval:
            # per-boundary codims
            L = len(T)
            terms = []
            for j in range(L):
                tprev = M[0] if j == 0 else T[j-1]
                terms.append((tprev - T[j]) * (M[j+1] - T[j]))
            out.append((T, terms))
    return mval, out

# ---- anchors from Lambda.lean docstring ----
anchors = {
    (2,2,2): 3, (2,1,2): 2, (2,2,2,2): 3, (3,3,3,3): 6,
    (2,2,2,2) : None,  # placeholder
    (3,3,4): 8, (4,4,2,2): 4,
}
# note aoyagiLambda(2,2,2)=3/2 -> minAdm 3; (2,1,2)->1 lambda -> minAdm 2; (2,2,2,2) lambda 3/2 -> minAdm 3; (3,3,3,3) lambda 3 -> minAdm 6

print("=== anchor check: minAdm_brute vs minAdmRec vs expected ===")
for M, exp in [((2,2,2),3),((2,1,2),2),((2,2,2,2),3),((3,3,3,3),6),((3,3,4),8),((4,4,2,2),4)]:
    mb,_ = minAdm_brute(M)
    mr = minAdmRec(M)
    tag = "OK" if (mb==mr==exp) else "MISMATCH"
    print(f"  M={M}: brute={mb}  rec={mr}  expected={exp}   {tag}")

print("\n=== cross-check brute==rec over random chains (widths 0..4, L=2..5) ===")
import random
random.seed(1)
mism=0; N=6000
for _ in range(N):
    L = random.randint(2,5)
    M = tuple(random.randint(0,4) for _ in range(L+1))
    if minAdm_brute(M)[0] != minAdmRec(M):
        mism+=1
        if mism<=5: print("   MISMATCH", M, minAdm_brute(M)[0], minAdmRec(M))
print(f"  mismatches: {mism}/{N}")

print("\n=== binding paths + per-boundary decomposition (target cases) ===")
for M in [(2,2,2),(2,2,2,2),(3,3,3,3)]:
    mval, paths = binding_paths(M)
    print(f"  M={M}  minAdm={mval}")
    for T,terms in paths:
        print(f"     T*={T}  per-boundary={terms}  sum={sum(terms)}")
