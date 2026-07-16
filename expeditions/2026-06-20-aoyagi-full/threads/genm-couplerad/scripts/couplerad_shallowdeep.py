# CORRECTED threshold. W(S)=int_Acor det((Acor S)(Acor S)^T)^{-a/2} finite iff a < rank(S)-b+1
# <=> rank S > a+b-1 <=> rank S >= a+b (integers). SHALLOW: rank S >= a+b. DEEP: rank S <= a+b-1.
# (My earlier cert used rank S >= a+b-1 -- OFF BY ONE. schurrec caught it via W finite iff rank S>=2 for a=b=1.)
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
print("CORRECTED: shallow rank S >= a+b (W Wishart-finite); deep rank S <= a+b-1 (W diverges, coupled).")
for (M,u) in [((4,4,4,4),3),((5,5,5,5),4),((3,3,4,4),2),((3,4,5,4),2),((4,5,6,5),3)]:
    a=M[0]-u;b=M[1]-u;rho=min(M[2:]);n=M[-1];p=M[2] # p=M2 for arity4 single deep matrix; ranks up to min(M2,n)=rho
    shallow_rankS=[r for r in range(0,rho+1) if r>=a+b]
    deep_rankS=[r for r in range(0,rho+1) if r<=a+b-1]
    print(f"  M={M} u={u} a={a} b={b} rho={rho} a+b={a+b}: SHALLOW rank S in {shallow_rankS} (W finite, bolt-on) | DEEP rank S in {deep_rankS} (W=inf, coupled re-expression)")
    print(f"      => b={b}: deep region {'= {S=0} ONLY (measure-zero, near-trivial)' if (a+b-1)<1 else '= {rank S <= '+str(a+b-1)+'} (POSITIVE-codim -- needs coupled treatment, NOT all-shallow)'}")
