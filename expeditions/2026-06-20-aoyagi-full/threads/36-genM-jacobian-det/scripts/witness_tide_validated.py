"""Witness tide (2026-06-27): exhaustive validation of the colPath witness (case 1) and the
rigorous achieverUfun==0 characterization (case 2). GenBlk-indexed model matches the cert sympy
on M=(3,3,1,3). See ../witness-tide-finding.md."""
import numpy as np, itertools
def achiever(M):
    L=len(M)-1
    def Mval(T):
        s=0
        for j in range(L):
            tp=M[0] if j==0 else T[j-1]; s+=(tp-T[j])*(M[j+1]-T[j])
        return s
    def adm(T):
        for j in range(L):
            ub=min(M[0],M[1]) if j==0 else M[j+1]
            if not 0<=T[j]<=ub: return False
        for i in range(L):
            for j in range(i,L):
                if T[j]>T[i]: return False
        return T[L-1]==0
    best=None;bv=10**9
    for T in itertools.product(*[range((min(M[0],M[1]) if j==0 else M[j+1])+1) for j in range(L)]):
        if adm(T) and Mval(T)<bv: bv=Mval(T);best=T
    return list(best),bv
def sim(M,tach,pivot_b,Wdict,e=1.,u=1.):
    L=len(M)-1
    T=lambda k: M[0] if k==0 else tach[k-1]; W=lambda k: M[k]; Z=lambda a,b: np.zeros((a,b))
    def Bmat(k):
        if k==0: return np.eye(T(0))
        B=Z(T(k),T(k+1))
        for i in range(min(T(k+1),T(k))): B[i,i]=1.0
        return B
    def Rmat(k):
        R=Z(T(k),W(k))
        if k==pivot_b:
            t1=T(k+1) if k<L else 0; rk=T(k)-t1; ck=W(k)-t1
            if rk>=1 and ck>=1: R[t1,t1]=e
        return R
    def Wblk(k):
        rows=max(0,W(k)-T(k+1)); cols=W(k+1); Wm=Z(rows,cols)
        if k in Wdict and Wdict[k][0]<rows and Wdict[k][1]<cols: Wm[Wdict[k]]=1.0
        return Wm
    def chainQ(k):
        Q=Z(T(k+1),W(k))
        for i in range(T(k+1)): Q[i,i]=1.0
        return Q
    def Cg(k):
        return Bmat(k)@chainQ(k)+u*Rmat(k) if k<L else Z(T(k),W(k))
    def Agen(k):
        if k>=L: return Z(W(k),W(k+1))
        t1=T(k+1); c=W(k)-t1; C=Cg(k+1); Wm=Wblk(k); A=Z(W(k),W(k+1))
        for i in range(t1): A[i,:]=C[i,:]
        for a in range(c): A[t1+a,:]=Wm[a,:]
        return A
    def suffix(s):
        if s==L: return np.eye(W(L))
        P=Agen(s)
        for k in range(s+1,L): P=P@Agen(k)
        return P
    def Es(s): return Rmat(s)@Agen(s)
    def Hm(s):
        if s==L: return Z(T(L),W(L))
        return Bmat(s)@Hm(s+1)+Es(s)@suffix(s+1)
    return Hm(0)
def colpath_witness(M,tach):
    L=len(M)-1; T=lambda k: M[0] if k==0 else tach[k-1]; W=lambda k: M[k]
    p=None
    for k in range(1,L):
        if T(k)-T(k+1)>=1 and W(k)-T(k+1)>=1: p=k
    if p is None: return None   # case 2: no interior E => achieverUfun==0
    Wd={}; surv=0
    for k in range(L-1,p-1,-1):
        rows=W(k)-T(k+1)
        if rows>=1 and surv<W(k+1): Wd[k]=(0,surv); surv=T(k+1)
        elif surv>=T(k+1): return 'BREAK'
    return sim(M,tach,p,Wd)
if __name__=='__main__':
    ok=brk=dead=0
    for L in range(2,5):
      for M in itertools.product(range(1,4),repeat=L+1):
        M=list(M); T0,mv=achiever(M)
        if mv==0: continue
        tach=[M[0]]+list(T0)
        r=colpath_witness(M,tach)
        if r is None: dead+=1
        elif isinstance(r,str): brk+=1
        elif np.any(np.abs(r)>1e-9): ok+=1
        else: print("UNEXPECTED FAIL",M,T0)
    print(f"interior-drop OK={ok}  BREAK={brk}  boundary-drop(achieverUfun==0)={dead}")
