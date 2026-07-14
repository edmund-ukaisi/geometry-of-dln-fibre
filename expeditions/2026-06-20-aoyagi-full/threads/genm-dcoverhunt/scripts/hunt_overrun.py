"""DECISIVE HUNT.  For hcvg-FAILING sector chains (j=0, a*+b* > m=min(M1,Mlast)),
the TRUE corank-weight threshold is a+b <= rho_Z = deepRank = min(M2,...,Mlast)
(NOT a+b <= M2).  The corank weight
   Wenn(Z) = int_{A_cor in box} det((A_cor Z)(A_cor Z)^T)^{-a/2}
is:  +inf if rho_Z < b  (b x b gram of rank-<b matrix, det=0 identically);
     finite iff a+b <= rho_Z  (if rho_Z >= b);
     LOG-divergent at a+b = rho_Z+1.

OVER-RUN(deepRank) := a+b - deepRank.
  = 1  : borderline w.r.t. deepRank (log-divergent corank weight; theta-interp *might* salvage)
  >= 2 : genuine over-run (corank weight diverges polynomially; salvage to minAdm/2 in doubt)
  b > deepRank : HARD (identically-singular gram, det=0, weight = +inf outright)

Also compute, per chain, the exact threshold reachable by the theta-interpolation over
the deepRank-frame and compare to minAdm(M)/2.
"""
import itertools
from defs import (minAdm, bindingCut, tailMinWidth, redChain, deepRank,
                  a_star, b_star, is_good)

def scan(max_arity, wid):
    buckets = {}   # overrun value -> count
    hard = []      # b > deepRank : weight identically +inf
    overrun_ge2 = []
    for arity in range(4, max_arity + 1):
        for M in itertools.product(range(1, wid + 1), repeat=arity):
            if not is_good(M):
                continue
            t = bindingCut(M)
            if t < 1:
                continue
            a = a_star(M); b = b_star(M)
            if a < 1 or b < 1:
                continue
            M2 = M[2]
            m = min(M[1], M[-1])
            if m > M2:
                continue          # sector shell empty
            ab = a + b
            if ab <= m:
                continue          # hcvg holds -> off-sector m-frame route
            # hcvg FAILS: needs sector route
            dR = deepRank(M)
            overrun = ab - dR
            buckets[overrun] = buckets.get(overrun, 0) + 1
            if b > dR:
                hard.append((M, t, a, b, M2, m, dR, ab))
            if overrun >= 2:
                overrun_ge2.append((M, t, a, b, M2, m, dR, ab, overrun))
    return buckets, hard, overrun_ge2

if __name__ == "__main__":
    for wid in [6, 7, 8]:
        buckets, hard, o2 = scan(6, wid)
        print(f"=== widths 1..{wid}, arity 4..6 ===")
        print(f"OVER-RUN (a+b - deepRank) distribution over hcvg-failing sector chains:")
        for k in sorted(buckets):
            print(f"    a+b - deepRank = {k:>2} : {buckets[k]}")
        print(f"HARD (b > deepRank, corank weight identically +inf): {len(hard)}")
        for row in hard[:15]:
            print("     ", row)
        print(f"OVER-RUN >= 2 (corank weight polynomially divergent): {len(o2)}")
        for row in o2[:15]:
            print("     ", row)
        print()
