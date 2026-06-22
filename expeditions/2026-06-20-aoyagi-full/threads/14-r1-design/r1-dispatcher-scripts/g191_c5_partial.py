import sympy as sp
from itertools import product
def Mval(M,t):
    L=len(M)-1; tt=[M[0]]+list(t); return sum((tt[j-1]-tt[j])*(M[j]-tt[j]) for j in range(1,L+1))
def admissible(M,t):
    L=len(M)-1; tt=[M[0]]+list(t)
    if tt[-1]!=0: return False
    for j in range(1,L+1):
        if not(0<=tt[j]<=tt[j-1]): return False
        if tt[j]>M[j]: return False
    return True
def adm(M):
    L=len(M)-1; return [(t,Mval(M,t)) for t in product(*[range(M[0]+1)]*L) if admissible(M,t)]

# Find a GENUINE partial-drop: an admissible T with t_{s-1} > t_s > 0 for some s (so the active factor
# at step s has a PARTIAL rank drop on the prefix image — neither full-rank C2 nor zero/coupled C1).
print("Searching for genuine partial-drop strata (t_{s-1} > t_s > 0) in candidate M's:")
for M in [(3,3,2),(3,3,3),(3,2,2),(4,3,2),(3,3,2,2,2)]:
    strata = adm(M)
    for t,mv in strata:
        tt = [M[0]]+list(t)
        partials = [s for s in range(1,len(M)) if tt[s-1] > tt[s] > 0]
        if partials:
            print(f"  M={M}: T={t} has partial-drop at step(s) {partials} (tt={tt}), Mval={mv}")
    print()
