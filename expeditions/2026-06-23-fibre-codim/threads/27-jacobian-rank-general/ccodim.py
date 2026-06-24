#!/usr/bin/env python3
"""Exact replication of the engine's combinatorial C = cCodim(d, r) and the codimForm,
   to get GROUND-TRUTH C for reconciliation. Mirrors DLNFibre.Core.CTheta:
   - codimForm N m = sum_{1<=i<=u<=j<=v<=N} m[i-1,j-1] * m[u,v]
   - Kostant partitions of d with corner r: m: (a,b) -> N, supported on 0<=a<=b<=N,
     d[k] = sum_{a<=k<=b} m[a,b] for all k, m[0,N]=r.
   - cCodim = min over Kostant partitions of codimForm.
   - numTop = count of minimisers.
"""
from itertools import product as iproduct

def codimForm(N, m):
    # m : dict (a,b)->int for 0<=a<=b<=N ; codimForm sums over 1<=i<=u<=j<=v<=N
    tot = 0
    for i in range(1, N+1):
        for u in range(i, N+1):
            for j in range(u, N+1):
                for v in range(j, N+1):
                    tot += m.get((i-1, j-1), 0) * m.get((u, v), 0)
    return tot

def kostant_partitions(d, r):
    N = len(d)-1
    pairs = [(a,b) for a in range(N+1) for b in range(a, N+1)]
    # carrier: m[a,b] in 0..d[a] on triangle
    ranges = [range(d[a]+1) for (a,b) in pairs]
    parts = []
    for vals in iproduct(*ranges):
        m = {pairs[k]: vals[k] for k in range(len(pairs))}
        if m[(0,N)] != r:
            continue
        ok = True
        for k in range(N+1):
            s = sum(m[(a,b)] for (a,b) in pairs if a<=k<=b)
            if s != d[k]:
                ok = False; break
        if ok:
            parts.append(m)
    return parts

def cCodim(d, r):
    N = len(d)-1
    parts = kostant_partitions(d, r)
    if not parts:
        return None, 0, []
    vals = [(codimForm(N, m), m) for m in parts]
    mn = min(v for v,_ in vals)
    minimisers = [m for v,m in vals if v==mn]
    return mn, len(minimisers), minimisers

cases = [
    ([2,2,2],0),([2,2,2],1),([2,2,2],2),
    ([2,2,3],1),([3,2,3],1),
    ([3,3,3],1),([3,3,3],2),
    ([1,2,1],0),([1,2,1],1),
    ([2,2,2,2],1),([2,3,2],1),
    ([4,4,4],2),([3,4,3],1),
]
print(f"{'d':<14}{'r':<3}{'C=cCodim':<10}{'delta':<7}{'C+delta':<9}{'numTop':<8}")
for d,r in cases:
    N=len(d)-1
    C,ntop,mins = cCodim(d,r)
    dl = r*(d[N]+d[0]-r)
    print(f"{str(d):<14}{r:<3}{str(C):<10}{dl:<7}{str(None if C is None else C+dl):<9}{ntop:<8}")
