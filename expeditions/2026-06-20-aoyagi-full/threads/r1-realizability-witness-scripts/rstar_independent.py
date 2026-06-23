# Pin the INDEPENDENT r* definition and verify the genuine equality rankFn(cascade t*) = r*.
#
# r* is defined PURELY from (M, T*) via the running-rank vector and the window-min/survivors formula,
# with NO reference to any matrix. t* (the cascade's per-block survivor counts) = T* (Core t_p = Lambda T_p).
# The cascade prepends t_0 = M_0 (the identity prefix). So running ranks t = (M_0, T*_0,...,T*_{L-1}).
#
# DEFINITION (independent of cascade matrices):
#   tstar(M,T) : Fin(L+1) -> N  := s |-> if s=0 then M_0 else T[s-1]   (running ranks)
#   rstarFn(M,T) i j (i<=j) := survivors (M_j) (M_i) (windowMin over i<s<=j of tstar_s)
#                            = min (windowMin) (min (M_i) (M_j))
#     where windowMin over empty (i=j) = +inf so survivors = min(M_i,M_i)=M_i  (the diagonal = width).
#   rstarFn i j (i>j) := 0   (the rankFn off-triangle convention)
#
# This is EXACTLY the survivors/window-min formula that rankPattern_cascade_prefix proves the cascade
# realizes on the (0,j) row, EXTENDED to all (i,j) by the same window-min law — but defined from T*,M only.
import numpy as np
from itertools import product
INF = 10**9
def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
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

def tstar(M,T):  # running ranks t_0..t_L
    return [M[0]]+list(T)
def windowMin(t,i,j):  # min over i<s<=j; empty (i=j) -> INF
    if i==j: return INF
    return min(t[s] for s in range(i+1,j+1))
def rstarFn(M,T):  # independent r* as full 2-index pattern (0 off triangle)
    L=len(M)-1; t=tstar(M,T); R={}
    for i in range(L+1):
        for j in range(L+1):
            if i<=j:
                R[(i,j)]=min(windowMin(t,i,j), min(M[i],M[j]))
            else:
                R[(i,j)]=0
    return R

# matrix-side cascade rankFn (independent matrix build)
def partialId(r,c,t):
    Cm=np.zeros((r,c))
    for k in range(min(t,r,c)): Cm[k,k]=1.0
    return Cm
def rankFn_cascade(M,T):
    L=len(M)-1; tt=tstar(M,T)
    blocks=[partialId(M[s+1],M[s],T[s]) for s in range(L)]  # A_s rank = T[s] = t_{s+1}
    R={}
    for i in range(L+1):
        for j in range(L+1):
            if i<j:
                P=blocks[i].copy()
                for s in range(i+1,j): P=blocks[s]@P
                R[(i,j)]=int(round(np.linalg.matrix_rank(P,tol=1e-9)))
            elif i==j:
                R[(i,j)]=M[i]
            else:
                R[(i,j)]=0
    return R

# EXHAUSTIVE: for ALL admissible T (not just achievers), does rankFn(cascade T) == rstarFn(M,T)?
# (the equality is a property of the CASCADE realizing the window-min pattern, holds for all admissible T;
#  the achiever is just the T we instantiate at.)
fails=0; checked=0; ach_fails=0; ach_checked=0
for L in [2,3,4]:
    for M in product(range(1,5),repeat=L+1):
        M=list(M)
        mn,ach=achievers(M)
        for T in Adm(M):
            checked+=1
            Rc=rankFn_cascade(M,T); Rs=rstarFn(M,T)
            eq=all(Rc[k]==Rs[k] for k in Rc)
            if not eq: fails+=1
            if T in ach:
                ach_checked+=1
                if not eq: ach_fails+=1
print(f"checked {checked} admissible (L=2..4, widths 1..4): rankFn(cascade T) == rstarFn(M,T) fails = {fails}")
print(f"  of which ACHIEVER instances: {ach_checked} checked, {ach_fails} fails")
print()
# The GENUINE-EQUALITY scope: holds for ALL admissible T -> in particular for the achiever T*.
# Also verify the (0,j) row tie: rankFn(cascade) 0 j == cascadeCount 0 j == tstar_j
print("=== (0,j) row tie: rankFn(cascade) 0 j == tstar_j (the running ranks) ===")
for M,Tlab in [([2,3,4,3],"witness L=3"),([2,3,4,4,3],"witness L=4")]:
    mn,ach=achievers(M); T=ach[0]; t=tstar(M,T); Rc=rankFn_cascade(M,T); L=len(M)-1
    row=[Rc[(0,j)] for j in range(L+1)]
    print(f"  M={M} T*={T}: rankFn(0,j)={row}  tstar={t}  match={row==t}")
