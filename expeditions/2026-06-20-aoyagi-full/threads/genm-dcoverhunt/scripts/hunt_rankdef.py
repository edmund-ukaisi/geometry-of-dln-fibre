"""HUNT: good chains at the SECTOR borderline (a*+b* = M2+1) whose DEEP FACTOR is
rank-deficient (deepRank = min(M2,...,Mlast) < M2).

At such a chain the borderline lemma `corankOffSector_borderline_le` (needs Z.rank=M2)
and `uniformWenn_le` (needs ZZ^T >= eps^2 I, i.e. full row rank M2) BOTH have an
unmet full-rank hypothesis for the generic deep factor.

Also classify: does b* > deepRank (HARD divergence: A_cor*Z has rank <= deepRank < b*,
so the b*xb* gram is singular, det=0, det^{-a/2}=+inf) vs b* <= deepRank < M2 (marginal).
"""
import itertools
from defs import (minAdm, bindingCut, tailMinWidth, redChain, deepRank,
                  a_star, b_star, is_good)

def scan(max_arity, wid):
    hits_borderline_rankdef = []
    hits_sub_i_rankdef = []   # a+b<=M2 (sub-case i) with rank-deficient deep factor
    good_sector_all = 0
    good_borderline_all = 0
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
            q = min(M[1], M[-1])
            # sector shell j=0 nonempty:
            if q > M2:
                continue
            good_sector_all += 1
            dR = deepRank(M)
            ab = a + b
            if ab == M2 + 1:
                good_borderline_all += 1
                if dR < M2:
                    hits_borderline_rankdef.append((M, t, a, b, M2, dR, ab))
            elif ab <= M2:
                if dR < M2:
                    hits_sub_i_rankdef.append((M, t, a, b, M2, dR, ab))
    return (hits_borderline_rankdef, hits_sub_i_rankdef,
            good_sector_all, good_borderline_all)

if __name__ == "__main__":
    for wid in [5, 6, 7]:
        bl, subi, gs, gb = scan(6, wid)
        print(f"=== widths 1..{wid}, arity 4..6 ===")
        print(f"good chains w/ nonempty sector: {gs}; of which borderline (a+b=M2+1): {gb}")
        print(f"BORDERLINE + rank-deficient deep factor (deepRank<M2): {len(bl)}")
        for (M,t,a,b,M2,dR,ab) in bl[:20]:
            hard = "HARD(b>deepRank)" if b > dR else "marginal(b<=deepRank)"
            print(f"   M={M} t*={t} a*={a} b*={b} M2={M2} deepRank={dR} a+b={ab}={M2}+1  {hard}")
        print(f"SUB-CASE-i (a+b<=M2) + rank-deficient deep factor: {len(subi)}")
        for (M,t,a,b,M2,dR,ab) in subi[:20]:
            hard = "HARD(b>deepRank)" if b > dR else "marginal(b<=deepRank)"
            print(f"   M={M} t*={t} a*={a} b*={b} M2={M2} deepRank={dR} a+b={ab}<=M2  {hard}")
        print()
