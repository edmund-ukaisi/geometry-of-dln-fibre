"""
The descent step: given achievable s < r (same dim vector), is there an applicable linked
box move on m(r) whose drop rectangle D is contained in supp(r-s)?

We test EXHAUSTIVELY over all achievable pairs (s,r) with same d, small N, and check:
  (A) does *some* applicable linked box move on m(r) have D subset supp(g), g=r-s ?  [existence]
  (B) characterise a DETERMINISTIC, DIRECTLY-COMPUTABLE rule producing such a move.

Applicable linked box move on m=m(r): indices a<c<=b+1<=e with m[(a,e)]>=1 and (c>b or m[(c,b)]>=1).
Drop rectangle D(a,c,b,e) = {(i,j): a<=i<c, b<j<=e}.
"""
from box_engine import *
import itertools

def supp(g,N):
    return set((i,j) for i in range(N+1) for j in range(i,N+1) if g[(i,j)]>0)

def g_array(s,r,N):
    return {(i,j): r[(i,j)]-s[(i,j)] for i in range(N+1) for j in range(i,N+1)}

def applicable_moves(m,N):
    """All linked box moves (a,c,b,e) applicable to m."""
    out=[]
    for a in range(N+1):
        for e in range(a,N+1):
            for c in range(a+1,e+1):
                for b in range(c-1,e):
                    if not (a<c<=b+1<=e): continue
                    if m.get((a,e),0)<1: continue
                    if c<=b and m.get((c,b),0)<1: continue
                    out.append((a,c,b,e))
    return out

def drop_rect(a,c,b,e):
    return set((i,j) for i in range(a,c) for j in range(b+1,e+1))

def all_achievable_rank_patterns(d,N):
    """All rank patterns r achievable by some m>=0 with dim_vector(m)=d.
    Equivalently all m>=0 with that d; collect distinct r."""
    ivs=intervals(N)
    # m[(a,b)] bounded by min over t in [a,b] of d_t. Enumerate.
    # To keep finite: each m[(a,b)] in 0..max(d). Use constraint dim=d to prune via recursion.
    results={}
    # recursive fill
    def rec(idx, m):
        if idx==len(ivs):
            if dim_vector(m,N)==tuple(d):
                r=rank_pattern(m,N)
                key=tuple(r[(i,j)] for i in range(N+1) for j in range(i,N+1))
                results[key]=dict(m)
            return
        (a,b)=ivs[idx]
        # upper bound for this multiplicity: min_{t in [a,b]} (d_t - already used at t)
        cap=min(d)  # loose
        for val in range(cap+1):
            m[(a,b)]=val
            # prune: partial dim must not exceed d at any covered vertex already fully decided? hard; just cap
            rec(idx+1,m)
        m[(a,b)]=0
    rec(0,{})
    return results  # rankkey -> a representative m

def test_descent(d,N,verbose=False):
    pats=all_achievable_rank_patterns(d,N)
    rs=list(pats.values())
    # build rank dicts
    rdicts=[rank_pattern(m,N) for m in rs]
    fails=[]
    npairs=0
    for ri,r in enumerate(rdicts):
        m_r=rs[ri]
        moves=applicable_moves(m_r,N)
        for si,s in enumerate(rdicts):
            if si==ri: continue
            if not lt(s,r,N): continue
            npairs+=1
            g=g_array(s,r,N); S=supp(g,N)
            good=[mv for mv in moves if drop_rect(*mv).issubset(S) and len(drop_rect(*mv))>0]
            if not good:
                fails.append((s,r,g))
                if verbose: print("FAIL: no descent move", "s",{k:v for k,v in s.items()},"r",{k:v for k,v in r.items()})
    return npairs, fails

for d,N in [((1,2,1),2),((2,2,2),2),((1,2,2,1),3),((2,2,2,2),3),((1,2,3,2,1),4)]:
    npairs,fails=test_descent(list(d),N)
    print(f"d={d} N={N}: covering pairs s<r = {npairs}, descent-move-existence FAILURES = {len(fails)}")
