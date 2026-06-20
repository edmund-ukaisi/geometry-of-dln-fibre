"""
Sub-fact 2 deep exploration. For every covering pair s<r (same d), at the extremal cell (i0,j0):
  - verify the sharpening: SOME covering interval [a,e] (a<=i0,e>=j0) has m(r)>=1.
  - enumerate ALL valid (a,e): a<=i0, e>=j0, m(r)_{[a,e]}>=1, rect [a,i0]x[j0,e] subset supp(g).
  - characterise WHICH covering intervals are valid -> look for a forced/canonical choice.
"""
from box_engine import *
from descent_search import supp, g_array, all_achievable_rank_patterns

def extremal_cell(g, N):
    cells = [(i,j) for i in range(N+1) for j in range(i+1,N+1) if g[(i,j)]>0]
    if not cells: return None
    return min(cells, key=lambda ij:(ij[1], -ij[0]))

def rect_in_supp(g, N, a, i0, j0, e):
    for i in range(a, i0+1):
        for j in range(j0, e+1):
            if g.get((i,j),0) <= 0:
                return False
    return True

def covering_intervals(m_r, i0, j0, N):
    """[a,e] with a<=i0, e>=j0, m(r)>=1."""
    out=[]
    for a in range(0, i0+1):
        for e in range(j0, N+1):
            if m_r.get((a,e),0) >= 1:
                out.append((a,e))
    return out

def valid_intervals(m_r, g, i0, j0, N):
    out=[]
    for (a,e) in covering_intervals(m_r, i0, j0, N):
        if rect_in_supp(g, N, a, i0, j0, e):
            out.append((a,e))
    return out

def analyze(d, N, report_fails=True):
    pats = all_achievable_rank_patterns(list(d), N)
    rs = list(pats.values()); rdicts=[rank_pattern(m,N) for m in rs]
    pairs=0; sharpening_fail=0; subfact2_fail=0
    # which "selector" works: minimal-e, maximal-e, minimal-a, maximal-a, minimal-area, maximal-area
    for ri, m_r in enumerate(rs):
        r=rdicts[ri]
        for si, s in enumerate(rdicts):
            if si==ri or not lt(s,r,N): continue
            g=g_array(s,r,N); pairs+=1
            (i0,j0)=extremal_cell(g,N)
            cov=covering_intervals(m_r, i0, j0, N)
            if not cov:
                sharpening_fail+=1
                if report_fails: print("SHARPENING FAIL", d, "i0j0",(i0,j0))
            val=valid_intervals(m_r, g, i0, j0, N)
            if not val:
                subfact2_fail+=1
                if report_fails:
                    print("SUBFACT2 FAIL", d, "i0j0",(i0,j0),
                          "m_r",{k:v for k,v in m_r.items() if v},
                          "g",{k:g[k] for k in supp(g,N)})
    print(f"d={d} N={N}: pairs={pairs} sharpening_fail={sharpening_fail} subfact2_fail={subfact2_fail}")

if __name__=="__main__":
    for d,N in [((1,2,1),2),((2,2,2),2),((1,2,2,1),3),((2,2,2,2),3),
                ((1,2,3,2,1),4),((3,3,3,3),3),((1,1,1,1),3),((2,1,2,1),3)]:
        analyze(d,N)
