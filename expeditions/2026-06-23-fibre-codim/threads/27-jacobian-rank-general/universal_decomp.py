# Test the UNIVERSAL structural identity at EVERY fibre point (all profiles, top + singular):
#   V_orbit = T_E Mat^{<=r} = {M: bottom-right (dN-r)x(d0-r) block = 0}  (dim delta) is ALWAYS
#   contained in image(d mult_A), and  rank(d mult_A) = delta + dim pi_BR(image),
#   i.e. image = V_orbit (+) (image projected to BR block), a genuine direct sum.
# This is the clean structural decomposition. The '+C' is dim pi_BR(image), which = C at a top
# component and > C below. We test: (a) V_orbit subset image (image cap V_orbit = delta) at EVERY
# point; (b) rank = delta + dim pi_BR always.
import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros
from itertools import product as iproduct
import random
random.seed(7)
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
def test(d,r):
    N=len(d)-1; dN=d[N]; d0=d[0]; dl=r*(dN+d0-r)
    allok=True; checked=0
    for prof in iproduct(*[range(0,min(d[i+1],d[i])+1) for i in range(N)]):
        for _ in range(3):
            facs=[rk_rk(d[i+1],d[i],prof[i]) for i in range(N)]
            if chain(facs).rank()!=r: continue   # only points IN the fibre over rank-r
            J,out=jacJ(list(facs),d); rk=J.rank()
            cs=J.columnspace(); B=Matrix.hstack(*cs).T if cs else zeros(0,len(out))
            BR=[idx for idx,(rr,cc) in enumerate(out) if rr>=r and cc>=r]
            piBR=B[:,BR].rank() if B.rows>0 else 0
            cap=rk-piBR
            ok = (cap==dl) and (rk==dl+piBR)
            allok=allok and ok; checked+=1
            if not ok:
                print(f"   FAIL d={d} r={r} prof={prof}: rk={rk} δ={dl} piBR={piBR} cap={cap}")
            break
    print(f"d={d} r={r}: checked {checked} fibre points; V_orbit⊆image & rk=δ+π_BR  ALWAYS: {allok}")
for d,r in [([2,2,2],0),([2,2,2],1),([2,2,2],2),([2,2,3],1),([3,2,3],1),
            ([3,3,3],1),([3,3,3],2),([1,2,1],0),([1,2,1],1),([2,3,2],1)]:
    test(d,r)
