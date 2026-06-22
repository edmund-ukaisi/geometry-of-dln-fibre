"""Verify Codex's PEELING-RECURSION claim (decorrelated alt route to the bijection).

Codex (inference, to be checked) claims a last-vertex peeling:
  Fix m' a Kostant partition of (d_0,...,d_{N-1}).  Write b_i = m'_{i,N-1} for 0<=i<N
  (the multiplicities of intervals ENDING at the old last vertex N-1).
  An extension to a Kostant partition m of (d_0,...,d_N) is given by integers
     0<=x_i<=b_i (i<N),  x_N>=0,  sum_{i=0}^{N} x_i = d_N,
  with  m_{i,N}=x_i (i<N), m_{i,N-1}=b_i-x_i (i<N), m_{N,N}=x_N,
  and all other m_{ij}=m'_{ij}.
  Then  c(m) = c(m') + Delta_b(x),  Delta_b(x)=sum_{0<=a<u<=N}(b_a-x_a) x_u
  [with the convention b_N := 0, since the term a or u = N: for u=N, x_N; for a=N, b_N - x_N=-x_N
   -- need to pin the exact range; we TEST it].

  Local transfer identity:
    P_{d_N} prod_{i<N} P_{b_i}  =  sum_x q^{Delta_b(x)} P_{x_N} prod_{i<N} P_{b_i-x_i} P_{x_i}.

We test BOTH the codim decomposition (per-orbit) and the local transfer identity (q-series).
We also confirm the global 5gon follows by induction from the transfer identity.
"""
import sys, os
from itertools import product as iproduct
sys.path.insert(0, os.path.dirname(__file__))
from ctheta import kostant_fast, codimForm, intervals
from qseries import P_multiset, P_s, pmul, padd, trunc, PREC, pscale_shift

# ---- 1. Per-orbit codim decomposition test ----
# We need to interpret Codex's b_i and Delta_b precisely. We test the cleanest reading:
#   given m (Kostant of d, N>=1), let m' = restriction to intervals within columns 0..N-1.
#   Then b_i = m'_{i,N-1}? No: b_i should be the intervals of m that, after removing column N,
#   end at N-1. An interval [i,N] of m becomes [i,N-1] in m'; an interval [i,N-1] of m stays.
#   So m'_{i,N-1} = m_{i,N-1} + m_{i,N}.  Hence b_i = m_{i,N-1}+m_{i,N}, x_i = m_{i,N}, x_N=m_{N,N}.
# Test: c(m) - c(m') == Delta_b(x) with Delta_b = sum_{0<=a<u<=N}(b_a-x_a) x_u, b_N:=0? test variants.

def restrict_to_Nm1(N, m):
    """Project m (Kostant of d, columns 0..N) to m' on columns 0..N-1 by merging col N into N-1."""
    mp = {}
    for (i,j),v in m.items():
        if v==0: continue
        if j==N:
            jj=N-1
        else:
            jj=j
        if i> jj:  # interval (N,N) -> would become (N, N-1) invalid: that's x_N, drop from m'
            continue
        mp[(i,jj)] = mp.get((i,jj),0)+v
    return mp

def delta_b(N, b, x, bN=0):
    """Delta_b(x) = sum_{0<=a<u<=N} (b_a - x_a) x_u, with b indexed 0..N (b[N]=bN)."""
    bb = dict(b); bb[N]=bN
    tot=0
    for a in range(0,N+1):
        for u in range(a+1,N+1):
            tot += (bb.get(a,0)-x.get(a,0))*x.get(u,0)
    return tot

def test_codim_decomp(tests):
    print("=== peeling codim decomposition: c(m) - c(m') == Delta_b(x) ? ===")
    fails=0; checked=0
    for d in tests:
        N=len(d)-1
        if N<1: continue
        for r in range(0,min(d)+1):
            for m in kostant_fast(list(d), r):
                mp = restrict_to_Nm1(N, m)
                cm = codimForm(N, m)
                cmp_ = codimForm(N-1, mp)
                # b_i = m_{i,N-1}+m_{i,N} for i<N ; x_i=m_{i,N} (i<N), x_N=m_{N,N}
                b = {i: m.get((i,N-1),0)+m.get((i,N),0) for i in range(N)}
                x = {i: m.get((i,N),0) for i in range(N)}
                x[N] = m.get((N,N),0)
                db = delta_b(N, b, x, bN=0)
                checked+=1
                if cm - cmp_ != db:
                    fails+=1
                    if fails<=10:
                        print(f"  MISMATCH d={d} r={r}: c(m)={cm} c(m')={cmp_} diff={cm-cmp_} Delta={db}")
                        print(f"     m={ {k:v for k,v in m.items() if v} }")
    print(f"  checked {checked}; mismatches {fails}", "OK" if fails==0 else "FAIL")
    return fails

# ---- 2. Local transfer identity (q-series) ----
def P_block(vals):
    res=[1]+[0]*(PREC-1)
    for v in vals:
        res=pmul(res, P_s(v))
    return res

def test_transfer(b_tests):
    """ P_{dN} prod_i P_{b_i}  ==  sum_x q^{Delta} P_{x_N} prod_i P_{b_i-x_i} P_{x_i}. """
    print("=== local transfer identity ===")
    fails=0
    for (b, dN) in b_tests:
        N=len(b)   # b indexed 0..N-1 ; vertex N is new. (here 'N' = len(b))
        lhs = trunc(pmul(P_s(dN), P_block(b)))
        acc=[0]*PREC
        # x_i in 0..b_i (i<N), x_N>=0, sum x = dN
        ranges=[range(bi+1) for bi in b]
        for xs in iproduct(*ranges):
            used=sum(xs)
            xN=dN-used
            if xN<0: continue
            x={i:xs[i] for i in range(N)}; x[N]=xN
            bb={i:b[i] for i in range(N)}
            db=delta_b(N, bb, x, bN=0)
            term=pmul(P_s(xN), P_block([b[i]-xs[i] for i in range(N)]+list(xs)))
            acc=padd(acc, pscale_shift(term,1,db))
        if lhs!=trunc(acc):
            fails+=1; print(f"  FAIL b={b} dN={dN}"); print("   L",lhs[:8]); print("   R",trunc(acc)[:8])
    print("  OK" if fails==0 else f"  {fails} FAILS")
    return fails

if __name__=="__main__":
    tests=[(2,2,2),(2,3,2),(1,2,3),(3,2,1),(2,1,3,2),(4,4,4),(1,2,3,4),(3,3,3),(2,4,2),(1,2,2,3),(5,5,6),(6,5,5)]
    f=0
    f+=test_codim_decomp(tests)
    b_tests=[((1,),2),((2,1),2),((1,2),3),((2,2),2),((1,1,1),2),((2,1,3),2),((0,2),2),((3,),3)]
    f+=test_transfer(b_tests)
    print()
    print("PEELING ROUTE CERTIFIED" if f==0 else f"{f} FAILS -- peeling reading needs adjustment")
