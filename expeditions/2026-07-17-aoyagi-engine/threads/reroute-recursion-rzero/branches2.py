#!/usr/bin/env python3
"""FIXED: genuine Aoyagi branch profiles have t^{(L)}=0 (deepest layer fully degenerates at origin).
Verify: min_t Mval(t) over {t^{(L)}=0} == minAdm(M); additive accumulation identity; per-branch
recursion-consistency (a full branch = peel@t1 + a sub-branch of (t1,M3,...))."""
from functools import lru_cache
from fractions import Fraction

def Mval(M, t):
    L = len(M)-1
    assert len(t)==L
    s = (M[0]-t[0])*(M[1]-t[0])
    for j in range(2, L+1):
        s += (t[j-2]-t[j-1])*(M[j]-t[j-1])
    return s

def branches(M):
    """admissible profiles t=(t1..tL), t1<=min(M1,M2), t_j<=min(t_{j-1},M_{j+1}), and t_L=0."""
    L = len(M)-1
    if L==0: 
        yield (); return
    if L==1:
        yield (0,); return          # single factor: t^{(1)}=0 forced, Mval=M1*M2
    cap0 = min(M[0], M[1])
    def rec(j, prev, acc):
        if j==L:                    # last entry forced 0
            yield tuple(acc+[0]); return
        hi = min(prev, M[j])
        for tj in range(hi+1):
            yield from rec(j+1, tj, acc+[tj])
    yield from rec(1, cap0, [])

@lru_cache(None)
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

def report(M):
    allb=list(branches(M)); mA=minAdm(M)
    vals=[(t,Mval(M,t)) for t in allb]
    mv=min(v for _,v in vals)
    mins=[t for t,v in vals if v==mv]
    acc_ok=all(Mval(M,t)==(M[0]-t[0])*(M[1]-t[0])+Mval((t[0],)+tuple(M[2:]), t[1:]) for t in allb)
    print(f"M={M}: minAdm={mA} min_branch={mv} agree={mA==mv} | #branches={len(allb)} "
          f"minimizers={mins} rlct={Fraction(mv,2)} | acc_ident={acc_ok}")
    return mA,mins

for M in [(3,3,3,2,2),(3,3,4),(2,2,2),(2,2,2,2),(3,3,2,2),(4,4,2,2),(2,2,3,2),(4,4,4),
          (5,4,3,2,2),(2,3,4,5,6),(3,3,3,3,3),(6,2,5,3,4),(2,2)]:
    report(M)
