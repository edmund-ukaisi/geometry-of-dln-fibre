"""SECONDARY hunt: the 3-way cover routeMBox_le_shellSum branch hypotheses, per shell,
for ALL good chains.  Branches:
  j=0    (hsector)  -- needs sector route; at borderline a+b=m+1
  1<=j<r (hstrict)  -- deeperFlag_shell_le, needs hcvg: a+b <= m  (m=min(M1,Mlast)-j)
  j=r    (hsat)     -- saturated; a or b = 0 (corank-trivial)

Also check the FRAME-buildability m <= deepRank (deepRank=min(M2,...,Mlast)):
Brick F builds an m-frame only if Z_deep can retain m strong directions, i.e. m<=deepRank.

The routing case-split (Nat trichotomy j=0 / 0<j<r / j=r) is EXHAUSTIVE on [0,r] by
construction; the real question is whether each branch's HYPOTHESIS is met.
"""
import itertools
from defs import (minAdm, bindingCut, tailMinWidth, redChain, deepRank,
                  a_star, b_star, is_good)

def sub(x,y): return max(0,x-y)

def scan(max_arity, wid):
    offsector_hcvg_fail = []      # 1<=j<r good genuine nonempty with a+b > m  (hcvg fails)
    frame_fail = []               # any genuine nonempty shell with m > deepRank (frame unbuildable)
    sat_not_trivial = []          # j=r with a>=1 and b>=1 (NOT corank-trivial)
    off_count = 0
    for arity in range(4, max_arity + 1):
        for M in itertools.product(range(1, wid + 1), repeat=arity):
            if not is_good(M): continue
            t = bindingCut(M)
            if t < 1: continue
            astar = a_star(M); bstar = b_star(M)
            r = min(astar, bstar)
            dR = deepRank(M)
            for j in range(0, r+1):
                u = t + j
                a = sub(M[0], u); b = sub(M[1], u)
                genuine = (a>=1 and b>=1)
                q = min(M[1], M[-1])
                nonempty = (sub(q, j) <= M[2])
                m = sub(q, j)                        # frame dim = min(M1,Mlast)-j
                if not nonempty:
                    continue
                # frame buildability: only meaningful when shell can be nonempty & genuine
                if genuine and m > dR:
                    frame_fail.append((M, t, j, a, b, m, dR))
                if 1 <= j < r:
                    if genuine:
                        off_count += 1
                        if a + b > m:                # hcvg FAILS off-sector
                            offsector_hcvg_fail.append((M,t,j,a,b,m,dR,a+b))
                if j == r:
                    if a >= 1 and b >= 1:
                        sat_not_trivial.append((M,t,j,a,b))
    return offsector_hcvg_fail, frame_fail, sat_not_trivial, off_count

if __name__ == "__main__":
    for wid in [6, 7, 8]:
        offf, ff, sat, oc = scan(6, wid)
        print(f"=== widths 1..{wid}, arity 4..6 ===")
        print(f"OFF-SECTOR genuine shells (1<=j<r) checked: {oc}")
        print(f"  hcvg FAILS off-sector (a+b > m):  {len(offf)}")
        for row in offf[:15]: print("      ", row)
        print(f"FRAME UNBUILDABLE (genuine nonempty shell with m > deepRank): {len(ff)}")
        for row in ff[:15]: print("      ", row)
        print(f"SATURATED j=r NOT corank-trivial (a>=1 AND b>=1): {len(sat)}")
        for row in sat[:15]: print("      ", row)
        print()
