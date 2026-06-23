# DEEP analysis of candidate witnesses: verify the FULL 2-index rankFn(cascadeTuple) pattern,
# check the achiever's gate t_s <= M_s, and locate WHERE the window-min is non-trivial
# (an interior window i<=s<=j whose running-rank min is < both running-rank endpoints).
import numpy as np
from itertools import product

def admBound(M, j):
    return min(M[0], M[1]) if j == 0 else M[j+1]
def admPred(M, T):
    L = len(M)-1
    if any(T[j] > admBound(M,j) for j in range(L)): return False
    for i in range(L):
        for j in range(i,L):
            if T[j] > T[i]: return False
    if L>=1 and T[L-1]!=0: return False
    return True
def tPrev(M,T,j): return M[0] if j==0 else T[j-1]
def Mval(M,T):
    L=len(M)-1; return sum((tPrev(M,T,j)-T[j])*(M[j+1]-T[j]) for j in range(L))
def Adm(M):
    L=len(M)-1
    return [list(T) for T in product(*[range(admBound(M,j)+1) for j in range(L)]) if admPred(M,list(T))]
def achievers(M):
    adm=Adm(M); vals=[(T,Mval(M,T)) for T in adm]; mn=min(v for _,v in vals)
    return mn,[T for T,v in vals if v==mn]

# cascade running ranks t_0..t_L = (M_0, T_0,...,T_{L-1})
def tvec(M,T): return [M[0]]+list(T)

# the cascade itself (Core convention: A_s : Matrix(Fin d_{s+1})(Fin d_s); product is A_j..A_{i+1})
# rankFn d A i j = rank(submult i j); submult 0 j = A_{j-1}...A_0 ; window rank = min t over (i,j].
# We compute it by EXPLICIT matrix rank to be decorrelated, then compare to the window-min formula.
def partialId(r,c,t):  # diag(1^t,0) : r x c  (rows=d_{s+1}, cols=d_s)
    Cmat=np.zeros((r,c))
    for k in range(min(t,r,c)): Cmat[k,k]=1.0
    return Cmat
def cascade_blocks(M,t): # t = t_1..t_L (the per-block survivor counts); A_s rank = t_{s+1}=t[s]
    L=len(M)-1; return [partialId(M[s+1],M[s],t[s]) for s in range(L)]  # t indexed 0..L-1 = t_1..t_L
def rankFn_explicit(M,T):
    L=len(M)-1; tt=tvec(M,T); blocks=cascade_blocks(M,tt[1:])  # tt[1:] = T = t_1..t_L
    pat={}
    for i in range(L+1):
        for j in range(i,L+1):
            if i==j: pat[(i,j)]=M[i]
            else:
                P=blocks[i].copy()
                for s in range(i+1,j): P=blocks[s]@P
                pat[(i,j)]=int(round(np.linalg.matrix_rank(P,tol=1e-9)))
    return pat,tt
def windowmin_formula(M,T):
    L=len(M)-1; tt=tvec(M,T); exp={}
    for i in range(L+1):
        for j in range(i,L+1):
            exp[(i,j)] = M[i] if i==j else min(tt[s] for s in range(i+1,j+1))
    return exp

def interior_nontrivial_windows(M,T):
    # windows (i,j), i>0, j<L not forced, where min over (i,j] is < running-rank at i AND < at j (strict interior min)
    L=len(M)-1; tt=tvec(M,T); out=[]
    for i in range(1,L+1):
        for j in range(i+1,L+1):
            wm=min(tt[s] for s in range(i+1,j+1))
            if wm < tt[i] and wm < tt[j]:
                out.append(((i,j),wm,tt[i],tt[j]))
    return out

cands = {
  "(2,3,4,3)": [2,3,4,3],
  "(3,4,5,4)": [3,4,5,4],
  "(3,4,4,3)": [3,4,4,3],
  "(2,3,3,2)": [2,3,3,2],
  "(3,3,3,3)": [3,3,3,3],
  "(2,3,4,4,3)": [2,3,4,4,3],
}
for lab,M in cands.items():
    L=len(M)-1; mn,ach=achievers(M)
    incr=[s for s in range(L) if M[s]<M[s+1]]
    print(f"==== M={lab}  L={L}  minAdm={mn}  #achievers={len(ach)}  incr-steps={incr} ====")
    for T in ach:
        tt=tvec(M,T)
        # gate t_s <= M_s for s=0..L-1 (the submult_cascade_prefix ht hypothesis: t_p <= d_{p.castSucc}=M_p)
        gate=[(s, tt[s], M[s], tt[s]<=M[s]) for s in range(L)]  # NOTE: ht is on t_p = block rank = T[p-1]?? careful
        # Core ht: forall p:Fin N, t p <= d p.castSucc = M_p ; Core t_p = T[p] (Lambda). So check T[p] <= M[p].
        gateT=[(p, T[p], M[p], T[p]<=M[p]) for p in range(L)]
        gate_ok = all(g[3] for g in gateT)
        pat,_=rankFn_explicit(M,T); exp=windowmin_formula(M,T)
        match=all(pat[k]==exp[k] for k in pat)
        nz=sum(1 for x in T if x>0)
        interior=interior_nontrivial_windows(M,T)
        print(f"  T*={T}  runningRanks={tt}  #nonzero(T)={nz}")
        print(f"    gate T[p]<=M[p] (submult ht): {gateT}  -> all OK: {gate_ok}")
        print(f"    rankFn(cascade)==window-min over ALL (i,j): {match}")
        print(f"    INTERIOR (i>0) strict-min windows (i,j)|wm<both ends: {interior if interior else 'NONE (all windows trivial monotone)'}")
        # print the 2-index pattern
        for i in range(L+1):
            row=" ".join(f"{pat[(i,j)]:2d}" if j>=i else " ." for j in range(L+1))
            print(f"       i={i}: [{row}]")
    print()
