import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros
import random
random.seed(5)
def chain(f):
    M=f[-1]
    for k in range(len(f)-2,-1,-1): M=M*f[k]
    return M
def jac(facs,d):
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
    out=[(r,c) for r in range(dN) for c in range(d0)]
    cols=[(i,s,t) for i in range(N) for s in range(d[i+1]) for t in range(d[i])]
    J=zeros(len(out),len(cols)); S=[suf(i) for i in range(N)]; P=[pre(i) for i in range(N)]
    for ri,(rr,cc) in enumerate(out):
        for ci,(i,s,t) in enumerate(cols): J[ri,ci]=S[i][rr,s]*P[i][t,cc]
    return J
d=[2,2,2]; E=Matrix([[1,0],[0,0]])
def rinv(n):
    while True:
        M=randMatrix(n,n,min=-4,max=4)
        if M.det()!=0: return M
print("(2,2,2) r=1: branch A0 invertible, A1=E A0^-1:")
for _ in range(3):
    A0=rinv(2); A1=E*A0.inv()
    J=jac([A0,A1],d); print(f"  rkA0={A0.rank()} rkA1={A1.rank()} rank(dmult)={J.rank()} dim={4*2-J.rank()}")
print("(2,2,2) r=1: branch A1 invertible, A0=A1^-1 E:")
for _ in range(3):
    A1=rinv(2); A0=A1.inv()*E
    J=jac([A0,A1],d); print(f"  rkA0={A0.rank()} rkA1={A1.rank()} rank(dmult)={J.rank()} dim={8-J.rank()}")
