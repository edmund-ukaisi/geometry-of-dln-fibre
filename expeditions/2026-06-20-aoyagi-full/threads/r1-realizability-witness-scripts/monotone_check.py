# Is the achiever's running-rank vector (t_0,...,t_L)=(M_0,T_0,...,T_{L-1}) ALWAYS weakly decreasing?
# admPred forces T weakly decreasing AND T_0 <= min(M_0,M_1) <= M_0 = t_0. So t_0 >= T_0 >= T_1 >= ...
# => running ranks ALWAYS weakly decreasing for ANY admissible T (achiever or not). VERIFY exhaustively.
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

import itertools
viol_running=0; viol_total=0; checked=0
# sweep many M of L=2,3,4 with widths up to 5
for L in [2,3,4]:
    for M in product(range(1,6), repeat=L+1):
        M=list(M)
        for T in Adm(M):
            checked+=1
            t=[M[0]]+list(T)
            # running ranks weakly decreasing?
            if any(t[s] < t[s+1] for s in range(L)):  # t_s < t_{s+1} would be an INCREASE
                viol_running+=1
print(f"checked {checked} admissible vectors over L in 2..4, widths 1..5")
print(f"  running-rank-INCREASE violations (t_s < t_s+1): {viol_running}")
print("  => running ranks (M_0,T_0,...,T_{L-1}) are ALWAYS weakly DECREASING for admissible T." if viol_running==0
      else "  => NOT always monotone!")
# Consequence: window-min over (i,j] = t_j (right endpoint). So rankFn(i,j) = min(t_j, min(M_i,M_j)).
# For i=0: min(M_0,M_j) and t_j<=M_0 so = t_j (the running rank). For i>0: capped by min(M_i,M_j).
# Check: does the (0,j) row + the M-widths DETERMINE the full pattern (no independent interior info)?
print()
print("CONSEQUENCE: window-min over (i,j] = t_j (monotone), so")
print("  rankFn(i,j) = min(t_j, min(M_i, M_j)).  i=0 => t_j; i>0 => min(t_j, min(M_i,M_j)).")
