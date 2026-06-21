"""
Candidate provable mechanism: FIX e = e* (row-i0 maximal positive run end from j0), then CLIMB a.

Define e* = max e>=j0 s.t. g_{i0,j}>0 for all j in [j0,e].  (row-i0 run; e*>=j0 since g_{i0,j0}>0.)
Claim CLIMB-E*: exists a<=i0 with m(r)_{[a,e*]}>=1 and rect [a,i0]x[j0,e*] subset supp(g).
   The 'a' would be the smallest a<=i0 such that the rectangle stays in supp AND we hit m(r)>=1 by a=that.
Equivalent: among a in [0,i0] with [a,i0]x[j0,e*] subset supp(g) (an interval of a's, call [amin,i0]),
   some a in [amin,i0] has m(r)_{[a,e*]}>=1.

ALSO test symmetric: FIX a = a* (col-j0 maximal positive run up from i0), then EXTEND e.

ALSO test: the 'L-shaped' canonical: e* = row run, a* = col run, and check if ANY a in [a*,i0] x e* OR
   any e in [j0,e*] x a* works (the union of the two arms' rectangles).
"""
from box_engine import *
from descent_search import supp, g_array, all_achievable_rank_patterns

def extremal_cell(g,N):
    cells=[(i,j) for i in range(N+1) for j in range(i+1,N+1) if g[(i,j)]>0]
    return min(cells,key=lambda ij:(ij[1],-ij[0])) if cells else None
def rect_in_supp(g,a,i0,j0,e):
    return all(g.get((i,j),0)>0 for i in range(a,i0+1) for j in range(j0,e+1))

def rowrun_e(g,i0,j0,N):
    e=j0
    while e+1<=N and g.get((i0,e+1),0)>0: e+=1
    return e
def colrun_a(g,i0,j0,N):
    a=i0
    while a-1>=0 and g.get((a-1,j0),0)>0: a-=1
    return a

def test(d,N):
    pats=all_achievable_rank_patterns(list(d),N); rs=list(pats.values()); rd=[rank_pattern(m,N) for m in rs]
    pairs=0; climbE_ok=0; climbA_ok=0; either_ok=0
    fails_climbE=[]; fails_either=[]
    for ri,mr in enumerate(rs):
        r=rd[ri]
        for si,s in enumerate(rd):
            if si==ri or not lt(s,r,N): continue
            g=g_array(s,r,N); (i0,j0)=extremal_cell(g,N); pairs+=1
            estar=rowrun_e(g,i0,j0,N); astar=colrun_a(g,i0,j0,N)
            # CLIMB-E*: fix e=estar, vary a in [0,i0], need rect subset supp and m(r)>=1
            cE=False
            for a in range(0,i0+1):
                if rect_in_supp(g,a,i0,j0,estar) and mr.get((a,estar),0)>=1:
                    cE=True; break
            # CLIMB-A*: fix a=astar, vary e in [j0,N]
            cA=False
            for e in range(j0,N+1):
                if rect_in_supp(g,astar,i0,j0,e) and mr.get((astar,e),0)>=1:
                    cA=True; break
            climbE_ok+=cE; climbA_ok+=cA; either_ok += (cE or cA)
            if not cE and len(fails_climbE)<3:
                fails_climbE.append((dict((k,v) for k,v in mr.items() if v),{k:g[k] for k in supp(g,N)},(i0,j0),estar))
            if not (cE or cA) and len(fails_either)<4:
                fails_either.append((dict((k,v) for k,v in mr.items() if v),{k:g[k] for k in supp(g,N)},(i0,j0),(astar,estar)))
    print(f"d={d}: pairs={pairs} CLIMB-E*={climbE_ok} CLIMB-A*={climbA_ok} EITHER={either_ok}")
    for f in fails_either: print("    EITHER-FAIL", f)

if __name__=="__main__":
    for d,N in [((1,2,1),2),((2,2,2),2),((1,2,2,1),3),((2,2,2,2),3),((1,2,3,2,1),4),((3,3,3,3),3)]:
        test(d,N)
