"""
Structural probes on g = r - s (both cumulant patterns of nonneg arrays, same d).

PROBE A: is supp(g) a "staircase order ideal" toward the diagonal?
   If g_{ij}>0 and i<=i'<=j'<=j (sub-interval), is g_{i'j'}>0 ? (closed under shrinking interval)
PROBE B: convexity in rows / columns: if g_{ij}>0 and g_{ij''}>0 with j<j''*, is g positive in between? (run-connected)
PROBE C: the key local structure near extremal cell (i0,j0): what's g on column j0 (rows <= i0) and row i0 (cols >= j0)?
PROBE D: is r itself monotone? r_{ij} vs r_{i,j+1}, r_{i-1,j}? (cumulant monotonicities)
"""
from box_engine import *
from descent_search import supp, g_array, all_achievable_rank_patterns

def extremal_cell(g, N):
    cells = [(i,j) for i in range(N+1) for j in range(i+1,N+1) if g[(i,j)]>0]
    return min(cells, key=lambda ij:(ij[1], -ij[0])) if cells else None

def probe_A(d, N):
    """supp(g) closed under shrinking the interval (toward diagonal)?"""
    pats=all_achievable_rank_patterns(list(d),N); rs=list(pats.values()); rd=[rank_pattern(m,N) for m in rs]
    fails=[]
    for ri,mr in enumerate(rs):
        r=rd[ri]
        for si,s in enumerate(rd):
            if si==ri or not lt(s,r,N): continue
            g=g_array(s,r,N)
            for (i,j) in supp(g,N):
                for ip in range(i,j+1):
                    for jp in range(ip,j+1):
                        if ip<jp and i<=ip and jp<=j:
                            if g.get((ip,jp),0)<=0:
                                fails.append(((i,j),(ip,jp),{k:g[k] for k in supp(g,N)}))
    return fails

def probe_cumul_monotone(d,N):
    """For a cumulant r of nonneg m: r_{ij} - r_{i,j+1} >= 0 ? r_{ij}-r_{i-1,j}>=0 ?
       (i.e. r decreases as the interval [i,j] widens). And 2nd diff >=0 == m>=0."""
    pats=all_achievable_rank_patterns(list(d),N); rs=list(pats.values())
    bad_col=0; bad_row=0
    for mr in rs:
        r=rank_pattern(mr,N)
        for i in range(N+1):
            for j in range(i,N+1):
                # widen right: r_{i,j} >= r_{i,j+1}
                if j+1<=N and r[(i,j)] < r.get((i,j+1),0): bad_col+=1
                # widen left: r_{i,j} >= r_{i-1,j}
                if i-1>=0 and r[(i,j)] < r.get((i-1,j),0): bad_row+=1
    return bad_col, bad_row

def probe_C(d, N, maxshow=6):
    """near extremal cell: print column j0 (rows<=i0) and row i0 (cols>=j0)."""
    pats=all_achievable_rank_patterns(list(d),N); rs=list(pats.values()); rd=[rank_pattern(m,N) for m in rs]
    shown=0
    for ri,mr in enumerate(rs):
        r=rd[ri]
        for si,s in enumerate(rd):
            if si==ri or not lt(s,r,N): continue
            g=g_array(s,r,N); (i0,j0)=extremal_cell(g,N)
            col=[g.get((i,j0),0) for i in range(0,i0+1)]
            row=[g.get((i0,j),0) for j in range(j0,N+1)]
            # is column j0 (rows 0..i0) ALL positive? is row i0 (cols j0..?) a positive run then 0?
            col_allpos = all(v>0 for v in col)
            if shown<maxshow and (not col_allpos):
                print(f"  d={d} i0j0=({i0},{j0}) col_j0[0..i0]={col} row_i0[j0..]={row} g={{ {','.join(f'{k}:{g[k]}' for k in sorted(supp(g,N)))} }}")
                shown+=1
    return shown

if __name__=="__main__":
    print("=== PROBE A: supp(g) closed under shrinking interval? ===")
    for d,N in [((2,2,2),2),((1,2,2,1),3),((2,2,2,2),3),((1,2,3,2,1),4),((3,3,3,3),3)]:
        f=probe_A(d,N); print(f"d={d}: shrink-closure fails = {len(f)}", f[:2] if f else "")
    print("=== PROBE cumul monotone (r decreases as interval widens)? ===")
    for d,N in [((2,2,2),2),((1,2,2,1),3),((2,2,2,2),3),((3,3,3,3),3)]:
        print(f"d={d}: bad_col(widen-right)={probe_cumul_monotone(d,N)[0]} bad_row(widen-left)={probe_cumul_monotone(d,N)[1]}")
    print("=== PROBE C: column j0 below i0 all positive? (else printed) ===")
    for d,N in [((2,2,2),2),((1,2,2,1),3),((2,2,2,2),3),((1,2,3,2,1),4)]:
        n=probe_C(d,N); print(f"d={d}: examples-where-col-not-allpos shown={n}")
