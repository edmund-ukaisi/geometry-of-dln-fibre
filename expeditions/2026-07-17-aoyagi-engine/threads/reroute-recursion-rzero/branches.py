#!/usr/bin/env python3
"""Enumerate Aoyagi branch profiles t and their Mval (=codim S(t)) for a dimension vector,
find minAdm, identify minimizers, and verify the additive-accumulation identity that is the
core of the recursion-minimality (general-L) argument:
    Mval_full(t1, s) = (M1-t1)(M2-t1) + Mval_sub(s),
where s ranges over sub-branches of the depth-(L-1) problem (t1, M3,...,M_{L+1}).
All integer/exact."""
from functools import lru_cache
from fractions import Fraction

# widths M = (M^1, ..., M^{L+1}); profile t = (t^1,...,t^L) with t^j <= min(t^{j-1}, M_{j+1}), t^0:=min(M1,M2)
def Mval(M, t):
    # M has L+1 entries, t has L entries
    L = len(M)-1
    assert len(t)==L
    s = (M[0]-t[0])*(M[1]-t[0])
    for j in range(2, L+1):        # j = 2..L  (1-indexed)
        tprev = t[j-2]             # t^{(j-1)}
        tj    = t[j-1]             # t^{(j)}
        s += (tprev - tj)*(M[j] - tj)
    return s

def branches(M):
    """all admissible profiles t (weakly-decreasing, capped by widths)"""
    L = len(M)-1
    if L==0:
        yield ()
        return
    cap0 = min(M[0], M[1])
    def rec(j, prev, acc):
        if j> L:
            yield tuple(acc); return
        # t^{(j)} in [0, min(prev, M_{j+1})]  ; M_{j+1} = M[j] (0-indexed)
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
    print(f"==== M={M}  (L={len(M)-1}) ====")
    allb = list(branches(M))
    vals = [(t, Mval(M,t)) for t in allb]
    mA = minAdm(M)
    mv = min(v for _,v in vals)
    print(f"minAdm={mA}   min over enumerated branches={mv}   agree={mA==mv}")
    mins = [t for t,v in vals if v==mv]
    print(f"minimizer profiles (Mval={mv}, rlct={Fraction(mv,2)}): {mins}")
    # additive accumulation check: full branch (t1,s) vs peel + sub
    ok_acc=True
    for t in allb:
        t1=t[0]; s=t[1:]
        Msub=(t1,)+tuple(M[2:])   # sub widths (t1, M3,...)
        # s must be an admissible sub-branch of Msub
        full=Mval(M,t)
        peel=(M[0]-t1)*(M[1]-t1)
        sub =Mval(Msub, s) if len(Msub)>=1 and len(s)==len(Msub)-1 else None
        if sub is None:
            ok_acc=False; print("  SHAPE MISMATCH", t); continue
        if full != peel+sub:
            ok_acc=False
            print(f"  ACC FAIL t={t}: full={full} peel={peel} sub={sub}")
    print(f"additive accumulation Mval(t1,s)=(M1-t1)(M2-t1)+Mval_sub(s) for ALL branches: {ok_acc}")
    return mA, mins, ok_acc

for M in [(3,3,3,2,2),(3,3,4),(2,2,2),(2,2,2,2),(3,3,2,2),(4,4,2,2),(2,2,3,2),(4,4,4),
          (5,4,3,2,2),(2,3,4,5,6),(3,3,3,3,3),(6,2,5,3,4)]:
    report(M)
    print()
