from itertools import product
def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
def tPrev(M,T,j): return M[0] if j==0 else T[j-1]
def Mval(M,T): return sum((tPrev(M,T,j)-T[j])*(M[j+1]-T[j]) for j in range(len(T)))
def admPred(M,T):
    L=len(T)
    if any(T[j]>admBound(M,j) for j in range(L)): return False
    if any(i<=j and T[j]>T[i] for i in range(L) for j in range(L)): return False
    return T[L-1]==0
def Adm(M):
    L=len(M)-1
    return [tuple(T) for T in product(*[range(admBound(M,j)+1) for j in range(L)]) if admPred(M,list(T))]
def minAdm(M): A=Adm(M); return min(Mval(M,T) for T in A), A

# The C1 schurState step resolves the codim-1-defect at the front pivot. What codim does it ADD at root M0?
# Hypothesis (from g138/g34-g35): a C1 step on stratum boundary adds a divisor of codim = the per-step
# rank-defect contribution. The deepest (origin) stratum is T=0 (Mval M0 0 = the full codim), but the
# achiever minAdm is a SHALLOWER stratum. So the achiever path does NOT go all the way down the schurState
# chain to T=0 — it BRANCHES OFF at the achiever's rank profile.
# Verify: Mval(M0, 0) [the origin/full-collapse codim] vs minAdm:
for M in [(2,2,2),(3,3,3),(4,3,2),(3,3,3,3),(5,4,3,2),(4,4,4,4,4)]:
    m0,A = minAdm(M)
    L=len(M)-1
    Tzero = tuple([0]*L)
    mv_zero = Mval(M,Tzero)
    achievers=[T for T in A if Mval(M,T)==m0]
    # The achiever profile vs the all-zero. The schurState chain collapses fronts -> tends toward T=0 region.
    # The achiever has LARGER ranks held (e.g. (4,3,2): achiever (3,0) holds rank 3 at layer1).
    print(f"M={M}: Mval(M,0)={mv_zero} (origin codim), minAdm={m0}, achievers={achievers}")
    print(f"   -> achiever != origin: {Tzero not in achievers}; origin codim {'>' if mv_zero>m0 else '=='} minAdm")
