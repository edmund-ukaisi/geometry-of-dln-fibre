from itertools import product

def admBound(M, j):
    return min(M[0], M[1]) if j == 0 else M[j+1]
def tPrev(M, T, j):
    return M[0] if j == 0 else T[j-1]
def Mval(M, T):
    return sum((tPrev(M,T,j) - T[j]) * (M[j+1] - T[j]) for j in range(len(T)))
def admPred(M, T):
    L = len(T)
    if any(T[j] > admBound(M,j) for j in range(L)): return False
    if any(i<=j and T[j]>T[i] for i in range(L) for j in range(L)): return False
    if T[L-1] != 0: return False
    return True
def Adm(M):
    L = len(M)-1
    return [tuple(T) for T in product(*[range(admBound(M,j)+1) for j in range(L)]) if admPred(M,list(T))]
def minAdm(M):
    A = Adm(M); return min(Mval(M,T) for T in A), A

# The fm3 schurState C1 step: peels the 2 front vertices. Its blow-up center codim per step?
# From the cert (g138/g34-g35): a C1 coupled-defect blow-up of stratum S(t) has codim = Mval(t).
# But the *single* schurState chain corresponds to ONE T per chain (the all-front-collapse).
# The achiever T* is reached by the path whose pivot choices follow T*'s rank-drop profile.
# KEY CHECK: is the codim ACCUMULATED by appendDivisor down a path = Mval(M0, T_path)?
# In the achiever-only design (foldFamily): we need ONE leaf with minAdm in its codim list.
# The binding divisor for stratum T has codim = Mval(M0,T). So ONE branch cell whose
# codim = Mval(M0, T*) = minAdm suffices, regardless of the rest of the tree.
# So the real question: can routeStep, AT THE ROOT, emit a branch with a cell whose
# codim = minAdm and witness = <T*, T* in Adm, minAdm = Mval M0 T*>?  T* is qStar (green).
# That's a SINGLE PivotWitness at the root + the rest of the tree need only satisfy C>= (codim>=minAdm).

for M in [(2,2,2),(3,3,3),(4,3,2),(2,3,2),(3,3,3,3),(2,2,2,2),(5,4,3,2),(4,4,4,4,4)]:
    m0, A = minAdm(M)
    achievers = [T for T in A if Mval(M,T)==m0]
    # Can we realize a single PivotWitness at codim=m0? Yes iff exists T* in Adm with Mval=m0. Always true (m0 is the min, achieved).
    # The (C>=) for ALL other cells: every cell codim c must be Mval(M0,T) for SOME admissible T.
    # Equivalently c in {Mval(M0,T) : T in Adm}. List that achievable-codim set:
    codims = sorted(set(Mval(M,T) for T in A))
    print(f"M={M}: minAdm={m0}, achievers={achievers}, achievable codim set={codims}")
