#!/usr/bin/env python3
# provenance: threads/27-coupled-diagb (pnp coupled diag(b) certificate)
"""Combinatorial layer for the coupled instances (3,3,4) and (3,3,2,2), exact integers.

Confirms, for the record the ideal-identity work rests on:
  - minAdm and the FULL branch lattice (every admissible profile t, its Mval, ratio);
  - which minimisers are coupled (layer-1 corank c1=(M1-t1)(M2-t1)>0 with 0<t1<min(M1,M2))
    vs clean (c1=0);
  - the "coupled-only" property: (3,3,4) has NO clean minimiser; (3,3,2,2) DOES.
Exit 0 iff all asserted numbers reproduce.
"""
import sys
from functools import lru_cache
from itertools import product

def Mval(M, t):
    """M = reduced widths (M^1..M^{L+1}); t = (t_1..t_L) weakly-decreasing, t_L=0.
    Mval = (M1-t1)(M2-t1) + sum_{j>=2} (t_{j-1}-t_j)(M_{j+1}-t_j)."""
    L = len(M) - 1
    assert len(t) == L
    val = (M[0] - t[0]) * (M[1] - t[0])
    for j in range(2, L + 1):          # j = 2..L, 1-indexed
        tjm1 = t[j - 2]                 # t_{j-1}
        tj = t[j - 1]                   # t_j
        val += (tjm1 - tj) * (M[j] - tj)
    return val

def admissible_profiles(M):
    """weakly-decreasing t=(t_1..t_L), t_L=0, 0<=t_s<=min(M^1..M^{s+1}) (certified Def-3 cap)."""
    L = len(M) - 1
    caps = [min(M[:s + 2]) for s in range(L)]   # cap for t_{s+1} (1-indexed s+1) = min(M^1..M^{s+1})
    out = []
    for t in product(*[range(c + 1) for c in caps]):
        if t[-1] != 0:
            continue
        if all(t[i] >= t[i + 1] for i in range(L - 1)):
            out.append(t)
    return out

@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(int(x) for x in M)
    if len(M) == 1:
        return 0
    if len(M) == 2:
        return M[0] * M[1]
    return min((M[0] - t) * (M[1] - t) + minAdm((t,) + M[2:])
               for t in range(min(M[0], M[1]) + 1))

def report(M):
    L = len(M) - 1
    profs = admissible_profiles(M)
    vals = {t: Mval(M, t) for t in profs}
    mn = min(vals.values())
    minimizers = [t for t, v in vals.items() if v == mn]
    print(f"\n=== M={M}  (L={L}) ===")
    print(f"minAdm (recursion) = {minAdm(M)};  min over admissible-profile Mval = {mn}  "
          f"[match: {minAdm(M) == mn}]")
    print(f"rlct_core = {mn}/2 = {mn/2}")
    print(" profile t        Mval  ratio   layer1-corank c1=(M1-t1)(M2-t1)   kind")
    for t in sorted(profs, key=lambda x: (vals[x], x)):
        t1 = t[0]
        c1 = (M[0] - t1) * (M[1] - t1)
        clean = (c1 == 0)
        partial = (0 < t1 < min(M[0], M[1]))
        kind = "CLEAN(c1=0)" if clean else (f"COUPLED partial corank-{(M[0]-t1,M[1]-t1)}"
                                            if partial else f"radial/other corank-{(M[0]-t1,M[1]-t1)}")
        star = "  <== MIN" if vals[t] == mn else ""
        print(f"   {str(t):14s}  {vals[t]:4d}  {vals[t]/2:>4}    c1={c1:<3d}"
              f"  {kind}{star}")
    # coupled-only?
    min_kinds = []
    for t in minimizers:
        t1 = t[0]
        c1 = (M[0] - t1) * (M[1] - t1)
        if c1 == 0:
            min_kinds.append("clean")
        elif 0 < t1 < min(M[0], M[1]):
            min_kinds.append("coupled-partial")
        else:
            min_kinds.append("radial")
    has_clean_min = "clean" in min_kinds
    print(f" minimizers: {minimizers}  kinds={min_kinds}  "
          f"has-clean-minimiser={has_clean_min}")
    return mn, minimizers, has_clean_min

ok = True
# (3,3,4): L=2 RRR core, coupled-only
mn334, minz334, clean334 = report((3, 3, 4))
ok &= (mn334 == 8) and (minz334 == [(1, 0)]) and (clean334 is False)

# (3,3,2,2): L=3, min reachable by clean branch
mn3322, minz3322, clean3322 = report((3, 3, 2, 2))
ok &= (mn3322 == 4) and (clean3322 is True) and ((2, 1, 0) in minz3322)

# permutation-invariance spot check of minAdm
import itertools
for base in [(3, 3, 4), (3, 3, 2, 2), (2, 2, 3, 2)]:
    vs = {minAdm(tuple(p)) for p in itertools.permutations(base)}
    print(f"\nperm-invariance minAdm{base}: values over all orderings = {vs}  "
          f"[invariant: {len(vs)==1}]")
    ok &= (len(vs) == 1)

print(f"\nALL COMBINATORIAL ASSERTIONS: {'PASS' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
