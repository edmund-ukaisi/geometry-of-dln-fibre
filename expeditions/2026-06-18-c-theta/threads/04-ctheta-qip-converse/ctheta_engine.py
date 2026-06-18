import itertools
from fractions import Fraction
from collections import Counter

# Vertices 0..N. Intervals [a,b] with 0<=a<=b<=N. m[(a,b)] multiplicity.

def codimform(N, m):
    """Lean codimForm: sum_{1<=i<=u<=j<=v<=N} m[i-1,j-1]*m[u,v]."""
    tot = 0
    for i in range(1, N+1):
        for u in range(i, N+1):
            for j in range(u, N+1):
                for v in range(j, N+1):
                    tot += m.get((i-1, j-1), 0) * m.get((u, v), 0)
    return tot

def kostant_partitions(d, r):
    """All m: intervals [a,b], 0<=a<=b<=N, with m[a,b]>=0, m[0,N]=r,
       and for each vertex k: d[k] = sum_{a<=k<=b} m[a,b]. Brute force."""
    N = len(d) - 1
    intervals = [(a,b) for a in range(N+1) for b in range(a, N+1)]
    # bound each m[a,b] <= d[a] (since a in [a,b])
    # We enumerate by a DFS respecting Kostant constraints column by column is faster,
    # but for small cases brute over ranges is fine.
    # Use recursion over intervals with running column sums.
    res = []
    # order intervals; track partial column coverage
    def rec(idx, assign, colsum):
        if idx == len(intervals):
            if all(colsum[k] == d[k] for k in range(N+1)):
                res.append(dict(assign))
            return
        (a,b) = intervals[idx]
        # max we can add: limited by remaining capacity at each covered column
        cap = min(d[k] - colsum[k] for k in range(a, b+1))
        if (a,b) == (0,N):
            lo = hi = r
            if not (lo <= cap): return
        else:
            lo, hi = 0, cap
        for val in range(lo, hi+1):
            assign[(a,b)] = val
            for k in range(a, b+1): colsum[k] += val
            rec(idx+1, assign, colsum)
            for k in range(a, b+1): colsum[k] -= val
            del assign[(a,b)]
    rec(0, {}, [0]*(N+1))
    return res

def C_theta(d, r):
    kps = kostant_partitions(d, r)
    N = len(d)-1
    vals = [(codimform(N, m), m) for m in kps]
    cmin = min(v for v,_ in vals)
    mins = [m for v,m in vals if v == cmin]
    return cmin, len(mins), len(kps), mins

# --- sorted-d substitution map (Thm 6.1), weakly increasing d' ---
def m_of_e(dprime, e):
    """e indexed 1..N, sum e = d'_0.  M = sum_i e_i (I_{0,i-1}+I_{i,N}) + sum_j f_j I_{j,N},
       f_j = d'_j - d'_{j-1}.  Returns multiplicity dict on intervals."""
    N = len(dprime) - 1
    m = Counter()
    for i in range(1, N+1):
        if e[i] != 0:
            m[(0, i-1)] += e[i]      # I_{0,i-1}
            m[(i, N)]   += e[i]      # I_{i,N}
    for j in range(1, N+1):
        f = dprime[j] - dprime[j-1]
        if f != 0:
            m[(j, N)] += f
    return dict(m)

