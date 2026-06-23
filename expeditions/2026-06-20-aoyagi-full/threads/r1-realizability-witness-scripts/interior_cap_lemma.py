# The interior-row load-bearing inequality: for the clean r*(i,j)=t*_j to hold at i>0, need
#   t*_j <= M_i  for all 0 < i < j   (so survivors cap min(M_i,M_j) >= t*_j; combined with t*_j<=M_j).
# t*_j = T_{j-1}. For 0<i<j: need T_{j-1} <= M_i.
# CHAIN (from admPred): T weakly decreasing so T_{j-1} <= T_{i-1} (since i-1 <= j-1).
#   And admBound: T_{i-1} <= M_i for i-1>=1 (admBound(i-1)=M_{(i-1)+1}=M_i); for i-1=0 (i=1): T_0<=min(M_0,M_1)<=M_1=M_i.
#   So T_{j-1} <= T_{i-1} <= M_i.  -> t*_j <= M_i.  [the SAME weak-decrease ∘ admBound(i-1) chain]
# Verify exhaustively AND show the chosen witnesses make this chain non-trivial (T_{j-1} < T_{i-1} strict,
# or T_{i-1} < M_i strict -> the bound is not tautological).
from itertools import product
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
def tstar(M,T): return [M[0]]+list(T)

# exhaustive: T_{j-1} <= M_i for all 0<i<j, admissible?
viol=0; checked=0
for L in [2,3,4]:
    for M in product(range(1,6),repeat=L+1):
        M=list(M)
        for T in Adm(M):
            t=tstar(M,T)
            for i in range(1,L+1):
                for j in range(i+1,L+1):
                    checked+=1
                    if t[j] > M[i]: viol+=1
print(f"interior cap inequality t*_j <= M_i (0<i<j): checked {checked}, violations {viol}")
print("  => holds for all admissible T (the weak-decrease ∘ admBound(i-1) chain)." if viol==0 else "  FAILS!")
print()
# Witnesses: show the chain is non-tautological (a strict step somewhere)
for M in [[2,3,2,2],[3,4,2,3]]:
    L=len(M)-1
    from itertools import product as pr
    # recompute achiever
    def Mval(M,T):
        def tP(j): return M[0] if j==0 else T[j-1]
        return sum((tP(j)-T[j])*(M[j+1]-T[j]) for j in range(L))
    adm=Adm(M); vals=[(T,Mval(M,T)) for T in adm]; mn=min(v for _,v in vals); T=[Tt for Tt,v in vals if v==mn][0]
    t=tstar(M,T)
    print(f"WITNESS M={M} T*={T} t*={t}: interior cap chain (0<i<j): t*_j <= T_{{i-1}} <= M_i")
    for i in range(1,L+1):
        for j in range(i+1,L+1):
            Tim1 = (T[i-1] if i-1<L else None)
            print(f"   (i={i},j={j}): t*_j={t[j]} <= T_{{i-1}}={T[i-1]} <= M_i={M[i]}  "
                  f"[{'STRICT drop t*_j<T_{i-1}' if t[j]<T[i-1] else 'plateau'}; "
                  f"{'cap M_i>t*_j non-binding' if M[i]>t[j] else 'cap binds'}]")
