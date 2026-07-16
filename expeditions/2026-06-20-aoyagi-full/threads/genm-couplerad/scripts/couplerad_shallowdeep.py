# For each in-scope cell k (rank S = rho-k), is the charge Wishart-BOUNDABLE (shallow) or does it need
# joint co-resolution (deep)?  Wishart weight int_Acor det((Acor S)(Acor S)^T)^{-a/2} finite iff
# a < rank(S) - b + 1 = (rho-k) - b + 1, i.e. rho-k >= a+b-1, i.e. k <= rho-(a+b)+1.  Deep: k > rho-(a+b)+1.
from functools import lru_cache
import itertools
@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==2: return M[0]*M[1]
    m0,m1=M[0],M[1]; rest=M[2:]
    return min((m0-t)*(m1-t)+minAdm((t,)+rest) for t in range(0,min(m0,m1)+1))
def binding_cut(M):
    m0,m1=M[0],M[1]; rest=M[2:]; best=None;targ=None
    for t in range(0,min(m0,m1)+1):
        v=(m0-t)*(m1-t)+minAdm((t,)+rest)
        if best is None or v<best: best=v;targ=t
    return targ,min(m0-targ,m1-targ)
print("cell shallow/deep split: shallow k<=rho-(a+b)+1 (charge Wishart-bounded); deep needs co-resolution")
for (M,u) in [((4,4,4,4),3),((5,5,5,5),4),((3,3,4,4),2),((3,4,5,4),2),((4,5,6,5),3)]:
    a=M[0]-u;b=M[1]-u;rho=min(M[2:])
    kmax_shallow = rho-(a+b)+1
    shallow=[k for k in range(1,rho+1) if k<=kmax_shallow]
    deep=[k for k in range(1,rho+1) if k>kmax_shallow]
    # deep cells: rank S = rho-k < a+b-1. For b=1: deep only when rho-k<a, ie rank S<a.
    deep_rankS=[rho-k for k in deep]
    print(f"  M={M} u={u} a={a} b={b} rho={rho} a+b={a+b}: shallow k={shallow} | DEEP k={deep} (rank S={deep_rankS})  {'(deep=only S=0/low, b=1 trivial)' if b==1 else '(b>=2: positive-codim deep, needs recursion)'}")
