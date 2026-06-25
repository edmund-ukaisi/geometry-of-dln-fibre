import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros
import random
random.seed(3)
def chain(f):
    M=f[-1]
    for k in range(len(f)-2,-1,-1): M=M*f[k]
    return M
def jacJ(facs,d):
    N=len(facs);dN=d[N];d0=d[0]
    def suf(i):
        if i==N-1: return eye(facs[N-1].rows)
        M=facs[N-1]
        for k in range(N-2,i,-1):M=M*facs[k]
        return M
    def pre(i):
        if i==0: return eye(facs[0].cols)
        M=facs[i-1]
        for k in range(i-2,-1,-1):M=M*facs[k]
        return M
    out=[(rr,cc) for rr in range(dN) for cc in range(d0)]
    cols=[(i,s,t) for i in range(N) for s in range(d[i+1]) for t in range(d[i])]
    J=zeros(len(out),len(cols)); S=[suf(i) for i in range(N)]; P=[pre(i) for i in range(N)]
    for ri,(rr,cc) in enumerate(out):
        for ci,(i,s,t) in enumerate(cols): J[ri,ci]=S[i][rr,s]*P[i][t,cc]
    return J,out
def rk_rk(rows,cols,rk,lo=-4,hi=4):
    while True:
        L=randMatrix(rows,rk,min=lo,max=hi)
        if L.rank()==rk: break
    while True:
        Rm=randMatrix(rk,cols,min=lo,max=hi)
        if Rm.rank()==rk: break
    return L*Rm
d=[2,2,2]; r=1
# build a profile [1,1] point with product rank 1
while True:
    A0=rk_rk(2,2,1); A1=rk_rk(2,2,1)
    if chain([A0,A1]).rank()==1: break
# its product B = A1 A0, rank 1 -- NOT necessarily = E! The fibre is over B, not E.
B=chain([A0,A1])
print("product B =", B.tolist(), " rank", B.rank())
J,out=jacJ([A0,A1],d); rk=J.rank()
print("rank(d mult)=",rk)
# V_orbit at THIS point = T_B Mat^{<=r}, NOT T_E! The BR-block decomposition is w.r.t. B's row/col
# spaces, not the fixed E coordinates. THE BUG: BR-block coords are fixed [r:,r:] only valid when B=E.
# For a generic B (not =E), T_B Mat^{<=1} is a DIFFERENT subspace (depends on B's spaces).
print(">>> BUG IDENTIFIED: universal_decomp used fixed BR coords [r:,r:] but B != E here.")
print(">>> The decomposition image=V_orbit(+)BR only makes sense in E-coordinates (B=E).")
