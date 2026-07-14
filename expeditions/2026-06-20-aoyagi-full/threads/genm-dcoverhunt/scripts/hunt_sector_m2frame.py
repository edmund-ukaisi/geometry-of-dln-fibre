"""REFINED HUNT.  The SECTOR (j=0) route needs the FULL M2 frame precisely when
hcvg FAILS at j=0, i.e. a*+b* > m where m = min(M1,Mlast).  (When a*+b* <= m, the
off-sector m-frame bound shell_corankOffSector_le_unif applies and the deep factor
only needs rank >= m.)

For hcvg-FAILING sector chains, uniformWenn_le (sub-case i, a+b<=M2) and
corankOffSector_borderline_le (sub-case ii, a+b=M2+1) BOTH require the deep factor
Z (M2 x Mlast) at full ROW rank M2 (via ZZ^T >= eps^2 I resp. Z.rank=M2).
deepRank = min(M2,...,Mlast).

OBSTRUCTION iff a good chain has: j=0 genuine+nonempty, hcvg FAILS (a*+b* > m),
a*+b* <= M2+1 (sector-relevant), and deepRank < M2 (M2 frame floor empty).
"""
import itertools
from defs import (minAdm, bindingCut, tailMinWidth, redChain, deepRank,
                  a_star, b_star, is_good)

def scan(max_arity, wid):
    hcvg_fail_sector = 0
    subi_hcvgfail = 0     # a+b<=M2, hcvg fails
    subii_hcvgfail = 0    # a+b=M2+1, hcvg fails
    over_M2p1 = []        # a+b >= M2+2 : should be EMPTY (proven a*+b*<=M2+1)
    obstruction = []      # hcvg fails, a+b<=M2+1, deepRank<M2
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
            m = min(M[1], M[-1])       # frame dim at j=0 = min(M1,Mlast)
            if m > M2:                  # nonempty sector shell: m <= M2
                continue
            ab = a + b
            hcvg_holds = (ab <= m)
            if hcvg_holds:
                continue               # off-sector m-frame route applies
            # hcvg FAILS -> needs the FULL M2 frame
            hcvg_fail_sector += 1
            dR = deepRank(M)
            if ab >= M2 + 2:
                over_M2p1.append((M, t, a, b, M2, dR, ab))
            elif ab == M2 + 1:
                subii_hcvgfail += 1
                if dR < M2:
                    obstruction.append((M, t, a, b, M2, m, dR, ab, "borderline"))
            else:  # m < ab <= M2
                subi_hcvgfail += 1
                if dR < M2:
                    obstruction.append((M, t, a, b, M2, m, dR, ab, "subi"))
    return (hcvg_fail_sector, subi_hcvgfail, subii_hcvgfail, over_M2p1, obstruction)

if __name__ == "__main__":
    for wid in [5, 6, 7]:
        hf, si, sii, over, obs = scan(6, wid)
        print(f"=== widths 1..{wid}, arity 4..6 ===")
        print(f"hcvg-FAILING sector chains (need M2 frame): {hf}")
        print(f"   sub-case i  (m<a+b<=M2):   {si}")
        print(f"   sub-case ii (a+b=M2+1):    {sii}")
        print(f"   a+b>=M2+2 (should be 0):   {len(over)}  {over[:5]}")
        print(f"OBSTRUCTION (hcvg-fail sector, a+b<=M2+1, deepRank<M2): {len(obs)}")
        for row in obs[:30]:
            print("   ", row)
        print()
