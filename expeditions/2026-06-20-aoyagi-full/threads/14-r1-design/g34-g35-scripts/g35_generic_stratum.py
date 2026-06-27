import sympy as sp, numpy as np
from itertools import product
# Is the achiever (min Mval) stratum = the GENERIC (smallest-codim, largest-dim) stratum of {A1A2=0}?
# The dim of stratum S(t1,0) for (m,m,m): {rank A1 = t1, A2 in ker A1 (so rank A2 <= m-t1), rank(A1A2)=0}.
# dim S(t1) = dim{rank A1=t1} + dim{A2: cols in ker A1} = [t1(2m-t1)] + [m*(m-t1)].
# (rank-t1 mxm matrices: dim t1(2m-t1); A2 mxm with cols in a fixed (m-t1)-dim space: m*(m-t1)).
# codim = 2m^2 - dim.
def Mval(M,t):
    tt=[M[0]]+list(t); L=len(M)-1
    return sum((tt[j-1]-tt[j])*(M[j]-tt[j]) for j in range(1,L+1))
print("=== which stratum is GENERIC (max dim / min codim)? vs the Mval-achiever ===")
for m in [2,3]:
    M=(m,m,m); N=2*m*m
    print(f"  (m,m,m)=({m},{m},{m}), N={N}:")
    best=None
    for t1 in range(m+1):
        dimS = t1*(2*m-t1) + m*(m-t1)   # dim rank-t1 A1 + dim A2 in ker
        codim = N - dimS
        mv = Mval(M,(t1,0))
        print(f"    S({t1},0): dim={dimS}, codim={codim}, Mval={mv}")
    print()
# For (3,3,3): compute and see if generic (min codim) = Mval-achiever.
