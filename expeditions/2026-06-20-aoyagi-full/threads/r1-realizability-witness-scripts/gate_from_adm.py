# The cascade gate hypothesis ht for submult_cascade_prefix (and partialId_mul middle-dim bound):
#   ht : forall p:Fin L, t_p <= d_{p.castSucc} = M_p,  where Core t_p = T_p (Lambda).
# i.e. T_p <= M_p for all p. Verify this is DERIVABLE from admPred (the Adm -> ht lemma the formaliser needs).
# CHAIN: p=0: T_0 <= min(M_0,M_1) <= M_0.  p>=1: T_p <= T_{p-1} <= admBound(p-1)=M_p (weak-decrease ∘ admBound).
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
viol=0; checked=0
for L in [2,3,4,5]:
    for M in product(range(1,5),repeat=L+1):
        M=list(M)
        for T in Adm(M):
            checked+=1
            if any(T[p]>M[p] for p in range(L)): viol+=1
print(f"gate T_p <= M_p (p:Fin L) from admPred: checked {checked} (L=2..5,widths 1..4), violations {viol}")
print("  => Adm -> (forall p, T_p <= M_p) is a clean derivable lemma (the cascade ht)." if viol==0 else "  FAILS")
