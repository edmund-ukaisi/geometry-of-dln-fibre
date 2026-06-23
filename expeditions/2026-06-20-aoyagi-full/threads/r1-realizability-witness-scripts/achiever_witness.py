# EXACT (integer) computation of Adm / Mval / minAdm / achiever set, decl-grounded against
# Lambda.lean (Adm, Mval, admBound, admPred, tPrev) and CascadeRank/CascadeRealizable.
#
# Lambda.lean (verbatim):
#   M : Fin(L+1) -> N    (the REDUCED widths M^{(s)} = H^{(s)} - r; here we feed M directly, r=0 case)
#   T : Fin L -> N       (the exponent vector, 0-indexed over Fin L)
#   tPrev M T j = (j=0 ? M 0 : T (j-1))        [over Z]
#   Mval M T = sum_{j:Fin L} (tPrev M T j - T j) * (M (j+1) - T j)     [over Z]
#   admBound M j = (j=0 ? min(M 0, M 1) : M (j+1))
#   admPred M T = (forall j, T j <= admBound j) AND (T weakly-DECREASING: i<=j -> T j <= T i)
#                 AND (forall j, j = L-1 -> T j = 0)
#   Adm M = { T : all admPred }   (finite: T j in 0..admBound j)
#   minAdm = inf over Adm of Mval
from itertools import product

def admBound(M, j):
    L = len(M) - 1
    if j == 0:
        return min(M[0], M[1])
    else:
        return M[j+1]

def admPred(M, T):
    L = len(M) - 1
    # T : list of length L
    if any(T[j] > admBound(M, j) for j in range(L)):
        return False
    # weakly decreasing: i<=j => T[j] <= T[i]
    for i in range(L):
        for j in range(i, L):
            if T[j] > T[i]:
                return False
    # last exponent zero: j = L-1 => T[j]=0
    if L >= 1 and T[L-1] != 0:
        return False
    return True

def tPrev(M, T, j):
    return M[0] if j == 0 else T[j-1]

def Mval(M, T):
    L = len(M) - 1
    s = 0
    for j in range(L):
        s += (tPrev(M, T, j) - T[j]) * (M[j+1] - T[j])
    return s

def Adm(M):
    L = len(M) - 1
    out = []
    ranges = [range(admBound(M, j) + 1) for j in range(L)]
    for T in product(*ranges):
        if admPred(M, list(T)):
            out.append(list(T))
    return out

def achievers(M):
    adm = Adm(M)
    vals = [(T, Mval(M, T)) for T in adm]
    mn = min(v for _, v in vals)
    ach = [T for T, v in vals if v == mn]
    return mn, ach, adm

# The cascade running-rank vector for an achiever T (the (0,j) row of rankFn(cascadeTuple)):
#   t_0 = M_0,  t_s = T[s-1] for s=1..L   (Core t_s = Lambda T s, with t_0 prepended = M_0)
# i.e. the running ranks r*(0,j) = t_j where (t_0,...,t_L) = (M_0, T_0, ..., T_{L-1}).
def runningRanks(M, T):
    return [M[0]] + list(T)

# Number of distinct nonzero entries among (t_1,...,t_L) = T  -> measures "non-trivial window-min"
def nonzero_count(T):
    return sum(1 for x in T if x > 0)

print("=== Achiever survey (exact integer Mval; r=0, M fed directly) ===\n")
cases = [
    [2,2,2], [3,2,3], [2,1,2], [3,3,3], [4,3,2], [3,3,3,3],
    [2,3,2], [2,3,3], [3,4,3], [2,2,3], [1,2,2], [2,3,4],
    [3,3,4], [2,4,3], [4,4,4], [3,4,5], [2,3,4,3], [3,4,4,3],
    [2,4,4,2], [3,4,5,4], [2,3,3,2], [4,5,4], [2,4,2],
]
for M in cases:
    L = len(M) - 1
    mn, ach, adm = achievers(M)
    incr = [s for s in range(L) if M[s] < M[s+1]]  # increasing-width steps M_s < M_{s+1}
    # report achievers with >=2 nonzero T entries (non-trivial window-min)
    rich = [(T, runningRanks(M,T)) for T in ach if nonzero_count(T) >= 2]
    print(f"M={M}  L={L}  minAdm={mn}  #Adm={len(adm)}  incr-steps(M_s<M_s+1)={incr}")
    for T in ach:
        nz = nonzero_count(T)
        print(f"     achiever T*={T}  Mval={Mval(M,T)}  runningRanks(0,j)={runningRanks(M,T)}  #nonzero(T)={nz}")
    print()
