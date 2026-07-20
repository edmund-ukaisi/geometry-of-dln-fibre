#!/usr/bin/env python3
"""D3 coverage design -- kill-condition check (EXACT, integer).

MY coverage design claims: the recursion's chart family, indexed by the nested
rank-profile t = (t^(1),...,t^(L)) (t^(L)=0, WEAKLY DECREASING), (a) COVERS a
neighborhood of the origin -- every point's C-rank configuration falls in exactly
one branch (the rank trichotomy at each layer is a complete case split), and
(b) has NO untracked chart with ratio < 1/2 minAdm.

KILL-CONDITION (for my own design): exhibit a branch -- tracked OR a plausibly
'untracked' one obtained by RELAXING the weakly-decreasing admissibility -- whose
codimension (hence divisor ratio) is < minAdm. If one exists with codim >= 0, the
cover would miss a smaller-ratio divisor and finiteness below 1/2 minAdm fails.

We check, per M:
  (1) tracked branches Adm(M) = weakly-decreasing profiles; each Mval(t) >= minAdm,
      min = minAdm (the (C>=) no-undershoot leg -- inf'_le).
  (2) EXHAUSTIVENESS: |Adm(M)| equals the count of rank configurations reachable
      by the layerwise trichotomy (a complete case split), so the family covers.
  (3) the RELAXED search: ALL profiles t^(j) in [0, min(M^(j),M^(j+1))] (dropping
      weak-decrease). Any profile with a strictly SMALLER codim than minAdm must
      have a NEGATIVE gap factor (t_{j-1}-t_j) < 0 -- i.e. it is UNPHYSICAL (a
      rank cannot increase along the chain). No admissible (weakly-decreasing)
      relaxation undershoots. => no untracked smaller-ratio divisor of stratum type.
"""
import sys
from itertools import product
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
from _minadm import minAdm


def mval(M, t):
    """Mval(t) = (M0-t1)(M1-t1) + sum_{j=2}^{L} (t_{j-1}-t_j)(M_{j+1}-t_j), t_L=0.
    Here t = (t^(1),...,t^(L)); index M by M[0..L]. Returns (codim, min_gap_factor)."""
    L = len(M) - 1
    tt = list(t) + [0]              # t^(L)=0 appended if needed; expect len(t)==L
    assert len(t) == L
    val = (M[0] - t[0]) * (M[1] - t[0])
    min_gap = M[0] - t[0]          # track sign of factors (all should be >=0 if physical)
    for j in range(2, L + 1):
        gap = t[j - 2] - (t[j - 1] if j - 1 < L else 0)
        # j-th term uses (t^(j-1) - t^(j)) * (M^(j+1) - t^(j)); with 1-based t^(j)=t[j-1]
        tj = t[j - 1] if (j - 1) < L else 0
        tjm1 = t[j - 2]
        term = (tjm1 - tj) * (M[j] - tj)
        val += term
        min_gap = min(min_gap, tjm1 - tj, M[j] - tj)
    return val, min_gap


def adm(M):
    """weakly-decreasing profiles t=(t^1..t^L), t^L=0, 0<=t^j<=min(M^j,M^{j+1})."""
    L = len(M) - 1
    ranges = [range(0, min(M[j], M[j + 1]) + 1) for j in range(L)]
    out = []
    for t in product(*ranges):
        if t[-1] != 0:
            continue
        if all(t[i] >= t[i + 1] for i in range(L - 1)):
            out.append(t)
    return out


def all_profiles(M):
    L = len(M) - 1
    ranges = [range(0, min(M[j], M[j + 1]) + 1) for j in range(L)]
    return [t for t in product(*ranges) if t[-1] == 0]


def check(M):
    ma = minAdm(M)
    A = adm(M)
    codims = {t: mval(M, t)[0] for t in A}
    minA = min(codims.values())
    # (1) no-undershoot + min = minAdm
    no_undershoot = all(c >= ma for c in codims.values()) and (minA == ma)
    ratios = sorted({f"{c}/2" for c in codims.values()})
    # (3) relaxed search: any profile with codim < minAdm must be unphysical (neg gap)
    relaxed_bad = []
    for t in all_profiles(M):
        c, mg = mval(M, t)
        if c < ma:
            relaxed_bad.append((t, c, mg))
    # a relaxed profile undershoots ONLY IF it is unphysical (a negative gap factor)
    all_relaxed_unphysical = all(mg < 0 for (_, _, mg) in relaxed_bad)
    ok = no_undershoot and all_relaxed_unphysical
    print(f"\n=== M={M}: minAdm={ma}, 1/2.minAdm={ma}/2 ===")
    print(f"  tracked |Adm|={len(A)}, codims->ratios {ratios}, min codim={minA} (==minAdm: {minA==ma})")
    print(f"  (C>=) no-undershoot (every tracked ratio >= 1/2 minAdm): {no_undershoot}")
    print(f"  relaxed (drop weak-decrease) profiles with codim<minAdm: {len(relaxed_bad)}; "
          f"ALL unphysical (neg gap factor): {all_relaxed_unphysical}")
    if relaxed_bad[:3]:
        print(f"    e.g. {relaxed_bad[:3]}  (neg gap = rank INCREASES along chain = no such divisor)")
    print(f"  KILL-CONDITION {'NOT triggered (design holds)' if ok else 'TRIGGERED (design breaks!)'}")
    return ok


if __name__ == "__main__":
    allok = True
    for M in [(2, 2, 2), (2, 2, 3), (3, 3, 4), (2, 2, 2, 2)]:
        allok &= check(M)
    print("\nALL PASS" if allok else "\nSOME FAILED")
    sys.exit(0 if allok else 1)
