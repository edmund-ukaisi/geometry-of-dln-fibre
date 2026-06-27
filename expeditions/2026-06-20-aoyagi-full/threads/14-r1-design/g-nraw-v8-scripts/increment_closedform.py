"""Closed form for the TRUE per-node increment  d(M) = minAdm(M) - minAdm(schurStateRed M),
   on the BINDING branch (minAdm < M0*M1).  schurStateRed = (M0-1, M1-1, M2,...,M_L).

Hypotheses to test:
 (H1) d = M_last          [cert-104b: FALSE for L>=3 generally]
 (H2) d relates to the minimizer T* of minAdm(M):  for the argmin exponent T*, the FIRST factor
      contributes (M0 - t1)(M1 - t1).  Conjecture: d = the marginal codim from the FIRST pivot drop.
 (H3) Try:  d = min over the realizable first-exponent of something.  Let's just DATA-MINE d and
      compare to candidate closed forms:  M_last, M1, t1*(...), and the 'first block' contribution.

We also test the cleaner recursion the g156/integration route actually uses (per cert text):
 child = red M = (M0-1, M1-1, tail)  (SAME as schurStateRed), and the node value is
 min( M0*M1 , nReg + minAdm(child) ) with nReg = the REGULAR-block dim, possibly = min(M0*M1 - R, n)
 NOT M_last.  Test  nReg := r*(H0 + Hlast - r) ... but here all-zero so r-structure differs.
"""
from itertools import product
from minadm import min_adm, argmin_adm, mval, adm_list

def child(M):
    M=list(M); M[0]-=1; M[1]-=1; return tuple(M)

print("Data-mine d on binding nodes (minAdm<mk).  Compare d to M_last and to (minAdm value chain).")
print("Also show the argmin T* of M to see what 'd' measures.\n")
for M in [(2,2,2),(3,3,3),(2,2,4),(2,3,4),(3,2,5),
          (2,2,2,2),(3,3,3,3),(2,3,2,4),(2,2,3,3),(3,3,2,2),(2,4,3,2),
          (1,2,1,2),(2,2,1,2),(2,1,3,2)]:
    L=len(M)-1; mk=M[0]*M[1]; ma=min_adm(M); ch=child(M); mc=min_adm(ch); d=ma-mc
    _,T=argmin_adm(M)
    binding = ma<mk
    print(f"  M={M} L={L} mk={mk} minAdm={ma}{' (BIND)' if binding else ' (cap)'} child={ch} minAdm(ch)={mc} d={d}  M_last={M[-1]}  argminT={T[:3]}")
