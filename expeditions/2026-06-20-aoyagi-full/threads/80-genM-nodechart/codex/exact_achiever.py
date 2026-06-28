"""
Exact-Aoyagi achiever finder + engine-tach mapping (decorrelated from extended.py's recursion).

Lean Adm/Mval (Foundations/Lambda.lean):
  T : Fin L -> N (length L);  tPrev(0)=M0, tPrev(j)=T[j-1];
  Mval(M,T) = sum_{j<L} (tPrev(j)-T[j])*(M[j+1]-T[j]);
  admBound(0)=min(M0,M1), admBound(j)=M[j+1] (j>=1);  T weakly decreasing; T[L-1]=0.
minAdm = min_{T in Adm} Mval.

Engine (RouteMGenChain): tach length L+1, tach[0]=M0, Text(0)=M0, Text(k+1)=tach[k].
The B_det family uses engine tach = (M0,) + T   (PREPEND M0, the identity boundary k=0).
So engine Text = [M0, M0, T0, T1, ..., T_{L-2}], Text(L)=T_{L-2}=tach[L-1].
"""
import itertools

def Mval(M,T):
    L=len(M)-1
    tP=lambda j: M[0] if j==0 else T[j-1]
    return sum((tP(j)-T[j])*(M[j+1]-T[j]) for j in range(L))

def admBound(M,j):
    return min(M[0],M[1]) if j==0 else M[j+1]

def adm_list(M):
    L=len(M)-1
    res=[]
    for T in itertools.product(*[range(admBound(M,j)+1) for j in range(L)]):
        if L>=1 and T[L-1]!=0: continue
        if any(T[j]>T[i] for i in range(L) for j in range(i,L)): continue
        res.append(T)
    return res

def minAdm(M):
    return min(Mval(M,T) for T in adm_list(M))

def achievers(M):
    """All Aoyagi achiever exponent vectors T (Fin L)."""
    mn=minAdm(M)
    return [T for T in adm_list(M) if Mval(M,T)==mn]

def engine_tach(M,T):
    """Engine descent tach (len L+1) = (M0,) + T. Text(0)=M0, Text(k+1)=tach[k]."""
    return (M[0],)+tuple(T)

def engine_text(M,tach):
    L=len(M)-1
    return [M[0]]+[tach[k] for k in range(L)]   # Text(0)=M0, Text(k+1)=tach[k] for k=0..L-1

if __name__=='__main__':
    for M in [(2,2,2),(2,1,2),(2,2,2,2),(3,3,3,3),(4,4,2,2),(3,3,4),(3,3,3,3,3)]:
        L=len(M)-1
        print('M=',M,'minAdm=',minAdm(M))
        for T in achievers(M):
            tach=engine_tach(M,T); Text=engine_text(M,tach)
            print('   Aoyagi T=',T,'-> engine tach=',tach,' engine Text=',Text,' Text(L)=',Text[L])
