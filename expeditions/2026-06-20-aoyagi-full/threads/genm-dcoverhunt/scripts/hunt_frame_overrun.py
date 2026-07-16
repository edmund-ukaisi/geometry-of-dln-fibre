"""SHARPER HUNT.  True shell nonemptiness: W = prod(tailChain M) is M1 x Mlast with
rank <= tailMinWidth = min(M1,...,Mlast).  So weakEigCount(W) >= min(M1,Mlast) - tailMinWidth;
shell-j is EMPTY for j < min(M1,Mlast) - tailMinWidth.  Frame dim on shell-j is
m = min(M1,Mlast) - j, buildable (connectable to the shell) only up to m <= (strong dirs of
Z_deep guaranteed on the shell) = m itself via Ky-Fan -- but the corank weight uses the m-frame,
whose convergent threshold is a+b <= m and borderline a+b = m+1.

The deep factor Z_deep (M2 x Mlast) has true rank deepRank = min(M2,...,Mlast) >= m on nonempty
shells, but the frame CONNECTABLE to shell-0 is only m-dimensional (shell-0 forces only m strong
dirs in Z_deep, not deepRank).  So the corank weight over the buildable m-frame has over-run
   OVERRUN_m := (a+b) - m .
  = 1 : m-frame borderline (log-div; theta-interp reaches minAdm/2 IF the reduced charge lines up)
  >=2 : POLYNOMIAL divergence over the buildable m-frame -> candidate GENUINE obstruction.

We test, over GOOD chains, NONEMPTY sector shells (j=0 with min(M1,Mlast)=tailMinWidth), whether
OVERRUN_m can be >= 2, i.e. whether m=min(M1,Mlast) < deepRank at an hcvg-failing sector.
"""
import itertools
from defs import (minAdm, bindingCut, tailMinWidth, redChain, deepRank,
                  a_star, b_star, is_good)

def sub(x,y): return max(0,x-y)

def scan(max_arity, wid):
    overrun_m = {}          # (a+b)-m distribution over nonempty hcvg-failing sector shells
    cand = []               # OVERRUN_m >= 2 candidates (m < deepRank)
    m_lt_deeprank = []      # nonempty sector with m < deepRank (any overrun)
    nonempty_sector = 0
    for arity in range(4, max_arity + 1):
        for M in itertools.product(range(1, wid + 1), repeat=arity):
            if not is_good(M): continue
            t = bindingCut(M)
            if t < 1: continue
            astar = a_star(M); bstar = b_star(M); r = min(astar, bstar)
            twmin = tailMinWidth(M)
            dR = deepRank(M)
            # sector j=0
            a = sub(M[0], t); b = sub(M[1], t)
            if not (a>=1 and b>=1): continue
            q = min(M[1], M[-1])
            m = q                                  # j=0 frame dim = min(M1,Mlast)
            # TRUE nonemptiness of shell-0: rank(W) can reach min(M1,Mlast), i.e. m <= tailMinWidth
            if m > twmin:
                continue                           # shell-0 EMPTY
            nonempty_sector += 1
            if a + b <= m:
                continue                           # hcvg holds at sector (convergent m-frame)
            ov = (a + b) - m
            overrun_m[ov] = overrun_m.get(ov, 0) + 1
            if m < dR:
                m_lt_deeprank.append((M,t,a,b,m,dR,twmin,a+b))
            if ov >= 2:
                cand.append((M,t,a,b,m,dR,twmin,a+b,ov))
    return overrun_m, cand, m_lt_deeprank, nonempty_sector

if __name__ == "__main__":
    for wid in [7, 8]:
        ov, cand, mld, ns = scan(6, wid)
        print(f"=== widths 1..{wid}, arity 4..6 ===")
        print(f"NONEMPTY sector shells (shell-0 not empty): {ns}")
        print(f"OVER-RUN over buildable m-frame ((a+b)-m) on hcvg-failing nonempty sectors: {dict(sorted(ov.items()))}")
        print(f"nonempty sector with m=min(M1,Mlast) < deepRank: {len(mld)}")
        for row in mld[:20]: print("     ", row)
        print(f"OVER-RUN_m >= 2 CANDIDATES (polynomial div over buildable frame): {len(cand)}")
        for row in cand[:20]: print("     ", row)
        print()
