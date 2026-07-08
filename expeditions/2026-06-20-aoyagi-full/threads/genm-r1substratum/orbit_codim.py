#!/usr/bin/env python3
"""
EXACT orbit codimension via the paper's Kostant-partition formula (eqn dim_formula, line 642):
  codim(O_m) = sum_{1<=i<=u<=j<=v<=N} m_{(i-1)(j-1)} * m_{uv}
Orbits of Rep_d (equioriented type A, N+1 nodes 0..N) <-> Kostant partitions:
  m_{ab} >= 0 for 0<=a<=b<=N   (multiplicity of the interval module supported on nodes a..b),
  subject to the dimension-vector constraint  sum_{a<=i<=b} m_{ab} = d_i   for every node i.
Rank pattern:  r_{ij} = rank of sub-product node i -> node j = sum_{a<=i, b>=j} m_{ab}  (i<=j).
The zero-product locus Sigma^0 = { r_{0N}=0 } = { m_{0N}=0 }.

We enumerate all Kostant partitions for d, compute codim, and confirm min codim over {m_{0N}=0}
equals minAdm.  We then read off the rank pattern of each orbit so we can identify the descent's
sub-generic Q_b strata and get their TRUE codim.
Validated against paper worked examples: (2,2,2)->3, (2,3,2)->4, (2,4,2)->4, (3,3,3)->7.
"""
from itertools import product as iproduct
import io, contextlib
_buf = io.StringIO()
with contextlib.redirect_stdout(_buf):
    import rankcharge as R

def arcs(N):
    return [(a, b) for a in range(N+1) for b in range(a, N+1)]

def node_dim(m, i, N):
    return sum(m[(a, b)] for (a, b) in arcs(N) if a <= i <= b)

def codim_kostant(m, N):
    total = 0
    for i in range(1, N+1):
        for u in range(i, N+1):
            for j in range(u, N+1):
                for v in range(j, N+1):
                    total += m[(i-1, j-1)] * m[(u, v)]
    return total

def rank_ij(m, i, j, N):
    """rank of sub-product node i -> node j (i<=j): intervals covering [i,j]."""
    return sum(m[(a, b)] for (a, b) in arcs(N) if a <= i and b >= j)

def enumerate_kostant(d):
    """all m_{ab}>=0 with node-dim constraints. Bounded: m_ab <= min(d[a..b])."""
    N = len(d) - 1
    A = arcs(N)
    ranges = [range(0, min(d[a:b+1]) + 1) for (a, b) in A]
    out = []
    for vals in iproduct(*ranges):
        m = dict(zip(A, vals))
        if all(node_dim(m, i, N) == d[i] for i in range(N+1)):
            out.append(m)
    return out

def sigma0(d):
    """orbits with r_{0N}=0 i.e. m_{0N}=0; return list of (m, codim)."""
    N = len(d) - 1
    return [(m, codim_kostant(m, N)) for m in enumerate_kostant(d) if m[(0, N)] == 0]

def sigma0_min(d):
    orbs = sigma0(d)
    if not orbs: return None, 0
    mn = min(c for _, c in orbs)
    return mn, sum(1 for _, c in orbs if c == mn)

if __name__ == "__main__":
    print("=== VALIDATE against paper worked examples (Sigma^0 min codim) ===")
    for d, expect in [((2,2,2),3),((2,3,2),4),((2,4,2),4),((3,3,3),7),
                      ((4,4,2),None),((3,3,3,4),None),((4,4,2,2),None),((2,4,1),None)]:
        mn, ncomp = sigma0_min(list(d))
        mAdm = R.minAdmRec(tuple(d))
        match = "== minAdm" if mn == mAdm else f"!= minAdm({mAdm}) !!!"
        tag = "" if expect is None or mn == expect else f"  EXPECTED {expect} !!!"
        print(f"  d={d}: Sigma^0 min codim={mn} (#topcomp={ncomp})  minAdm={mAdm} [{match}]{tag}")
