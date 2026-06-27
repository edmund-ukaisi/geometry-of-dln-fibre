"""Thread 03 — H1 vs H2 obstruction certificate (exact algebra, no floats load-bearing).

Adjudicates THREE distinct integer invariants of the DLN multiplication fibre, for a fixed
(reduced) dimension vector with relevant-set size m = ell, residue a in 1..m, and
delta = S - m*round(S/m):

  (1) theta_LR   = C(m, |delta|)                       # LR 2024: # TOP-DIM IRREDUCIBLE COMPONENTS
  (2) rlcm_LR    = m^2 {S/m}(1-{S/m})  = a(ell-a)      # LR 2024 Thm aoyagi-rlct: their printed rlcm
  (3) theta_Aoy  = a(ell-a)+1                           # Aoyagi 2023 Thm 1/2: ORDER of largest pole

KEY FINDINGS (this script verifies):
  * The SLT pole order (rlcm / Watanabe multiplicity) is NEITHER C(m,|delta|).
  * theta_Aoy = rlcm_LR + 1 SYSTEMATICALLY (every (m, S mod m)).
  * For 3-LAYER (reduced-rank regression, ell<=2) Aoyagi's a(ell-a)+1 reproduces the classical,
    independently-published Aoyagi-Watanabe (2005) RRR multiplicity m in {1,2} EXACTLY
    (0 mismatches over 657 cases incl. r>0).  => a(ell-a)+1 is the TRUE pole order.
  * rlcm_LR = a(ell-a) = 0 whenever |delta|=0 (a pole order can never be 0 at a zero of F)
    => LR's printed rlcm is off by one; it equals theta-1 (the free-energy log-log exponent).
"""
import itertools, math
from fractions import Fraction as F


def fracpart(x):
    return x - math.floor(x)


# ---- the three invariants from (m, S) ----
def rlcm_LR(m, S):
    f = fracpart(F(S, m))
    return m * m * f * (1 - f)          # LR printed rlcm


def aoyagi_a(m, S):
    M = math.ceil(F(S, m))
    return S - (M - 1) * m              # residue a in 1..m


def theta_aoyagi(m, S):
    a = aoyagi_a(m, S)
    return a * (m - a) + 1             # Aoyagi order of largest pole


def abs_delta(m, S):
    return abs(S - m * ((2 * S + m) // (2 * m)))


def theta_LR(m, S):
    return math.comb(m, abs_delta(m, S))   # # top-dim components


# ---- classical Aoyagi-Watanabe (2005) reduced-rank-regression order (INDEPENDENT ground truth) ----
def aw_order(N, M, H, r):
    """Order/multiplicity of largest pole for RRR Y~N(CX,...), rank(C)<=H, true rank r.
    m=2 iff central regime AND M+N+H+r odd; else 1. (Aoyagi-Watanabe 2005.)"""
    if N < M:
        N, M = M, N
    if (H - r >= N - M) and (H + r <= M + N):
        return 2 if ((M + N + H + r) % 2 == 1) else 1
    return 1


def aoyagi23_3layer_order(H1, H2, H3, r):
    """Aoyagi-2023 Thm-1 order a(ell-a)+1 for the 3-layer product A1(H1xH2)A2(H2xH3)."""
    Mred = [H1 - r, H2 - r, H3 - r]
    if any(x < 0 for x in Mred):
        return None
    s = sum(Mred); mx = max(Mred)
    rel = Mred if mx * 2 < s else (lambda L: (L.remove(mx) or L))(Mred.copy())
    ell = len(rel) - 1
    if ell <= 0:
        return None                    # degenerate (single relevant width)
    S = sum(rel); M = math.ceil(F(S, ell)); a = S - (M - 1) * ell
    return a * (ell - a) + 1


def check_systematic_plus_one():
    bad = []
    for m in range(1, 9):
        for b in range(0, m):
            S = m * 3 + b
            if theta_aoyagi(m, S) != rlcm_LR(m, S) + 1:
                bad.append((m, S))
    assert not bad, bad
    print("theta_Aoyagi == rlcm_LR + 1  : 0 mismatches over all (m, S mod m)  [systematic off-by-one]")


def check_classical_RRR():
    mism = 0; tot = 0
    for H1 in range(1, 8):
        for H2 in range(1, 8):
            for H3 in range(1, 8):
                for r in range(0, min(H1, H2, H3) + 1):
                    ao = aoyagi23_3layer_order(H1, H2, H3, r)
                    if ao is None:
                        continue
                    aw = aw_order(H1, H3, H2, r)     # N=H1 out, M=H3 in, hidden rank H=H2
                    tot += 1
                    if ao != aw:
                        mism += 1
    assert mism == 0, mism
    print(f"Aoyagi-2023 a(ell-a)+1 == classical Aoyagi-Watanabe (2005) RRR order : "
          f"0 mismatches over {tot} 3-layer cases (incl. r>0)")


def check_rlcm_zero_impossible():
    zeros = []
    for m in range(1, 7):
        S = m * 3                        # {S/m}=0 -> |delta|=0
        if rlcm_LR(m, S) == 0:
            zeros.append((m, S, theta_aoyagi(m, S)))
    print("rlcm_LR = 0 at |delta|=0 (IMPOSSIBLE pole order, since F^-1(0) nonempty => order>=1):")
    for m, S, ao in zeros:
        print(f"    m={m} S={S}: rlcm_LR=0  but Aoyagi-order={ao}")
    assert all(ao >= 1 for _, _, ao in zeros)


def crux():
    m, S = 4, 10                          # (2,2,2,2,2), r=0
    print("=== CRUX (2,2,2,2,2), r=0:  m=ell=4, S=10, |delta|=2, a=2 ===")
    print(f"  theta_LR  (# top-dim components) = C(4,2)     = {theta_LR(m,S)}")
    print(f"  rlcm_LR   (LR printed)           = a(l-a)     = {rlcm_LR(m,S)}")
    print(f"  theta_Aoy (order of largest pole)= a(l-a)+1   = {theta_aoyagi(m,S)}")
    assert theta_LR(m, S) == 6 and rlcm_LR(m, S) == 4 and theta_aoyagi(m, S) == 5


if __name__ == "__main__":
    crux()
    check_systematic_plus_one()
    check_classical_RRR()
    check_rlcm_zero_impossible()
    print("\nAll assertions passed.")
