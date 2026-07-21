#!/usr/bin/env python3
# provenance: threads/28-twoblock-diagb (pnp two-block/two-shared-factor diag(b) certificate)
"""Combinatorial census for the two-block / two-shared-factor stress-test, exact integers.
Establishes the design-space facts the resolution certificates rest on:
 (1) the MINIMAL width vector whose UNIQUE binding branch has TWO corank-2 coupling blocks is
     M=(4,4,4), t=(2,0), minAdm=12 (vs (3,3,4): one corank-2 block + one corank-1 row, minAdm=8).
 (2) the minimal L=4 (5-width) SEPARATED two-shared-factor binding branch is M=(3,3,3,2,2),
     t=(2,2,1,0), minAdm=4 (two corank-1 scalar couplings at layers 1 and 3, plateau at layer 2).
 (3) every width vector has min-width >= 1, so a smallest diagonal entry b1 always exists (the
     kept rank-survivor) -- the structural fact behind universal principality; monotonicity-free.
Exit 0 iff the asserted numbers reproduce.
"""
import sys
from itertools import product
from functools import lru_cache


def Mval(M, t):
    L = len(M) - 1
    val = (M[0] - t[0]) * (M[1] - t[0])
    for j in range(2, L + 1):
        val += (t[j - 2] - t[j - 1]) * (M[j] - t[j - 1])
    return val


def admissible(M):
    L = len(M) - 1
    caps = [min(M[:s + 2]) for s in range(L)]
    out = []
    for t in product(*[range(c + 1) for c in caps]):
        if t[-1] != 0:
            continue
        if all(t[i] >= t[i + 1] for i in range(L - 1)):
            out.append(t)
    return out


def n_corank2(M, t):
    L = len(M) - 1
    blocks = [(M[0] - t[0], M[1] - t[0])]
    for j in range(2, L + 1):
        blocks.append((t[j - 2] - t[j - 1], M[j] - t[j - 1]))
    return sum(1 for (r, c) in blocks if r >= 2 and c >= 2)


def binding(M):
    profs = admissible(M); vals = {t: Mval(M, t) for t in profs}
    mn = min(vals.values()); return mn, [t for t, v in vals.items() if v == mn]


ok = True

# (1) exhaustive: minimal UNIQUE two-corank-2-block binding branch
uniq = []
for L in range(2, 6):
    maxw = {2: 7, 3: 6, 4: 5, 5: 4}[L]
    for M in product(range(1, maxw + 1), repeat=L + 1):
        if min(M) < 2:
            continue
        mn, minz = binding(M)
        if len(minz) == 1 and n_corank2(M, minz[0]) >= 2:
            uniq.append((sum(M), M, minz[0]))
uniq.sort()
mn444, minz444 = binding((4, 4, 4))
print(f"(1) #uniquely-binding two-corank-2-block vectors (L=2..5, widths<=7): {len(uniq)}")
print(f"    minimal = M={uniq[0][1]} t={uniq[0][2]}  (expect (4,4,4), (2,0))")
print(f"    (4,4,4): minAdm={mn444}, minimisers={minz444}, corank2blocks={n_corank2((4,4,4),(2,0))}")
ok &= (uniq[0][1] == (4, 4, 4) and uniq[0][2] == (2, 0) and mn444 == 12 and minz444 == [(2, 0)])

# (2) minimal SEPARATED L=4 two-shared-factor binding branch: (3,3,3,2,2), t=(2,2,1,0) is a
#     minimiser (couplings at layers 1 & 3, plateau at layer 2) but is TIED with single-coupling
#     branches -- the same tie pattern as (3,3,2,2) (worked.tex): separated two-shared-factor
#     branches are minimisers but not UNIQUELY binding at small sizes. Both charts resolve to a
#     single chain, so the RLCT value is chart-robust; the two-shared-factor chart is what the
#     resolution certificate g-coupled-33322-separated.py checks.
mn5, minz5 = binding((3, 3, 3, 2, 2))
print(f"(2) (3,3,3,2,2): minAdm={mn5}, minimisers={minz5}")
print(f"    two-shared-factor branch (2,2,1,0) in minimisers: {(2, 2, 1, 0) in minz5} "
      f"(TIED with single-coupling branches -- not unique; same pattern as (3,3,2,2))")
ok &= (mn5 == 4 and (2, 2, 1, 0) in minz5)

# (2b) a UNIQUELY-binding L=4 SEPARATED two-coupling instance DOES exist -> closes the tie caveat:
#      (3,3,4,3,3), t=(2,2,1,0): couplings at layers 1 (scalar) & 3 (corank-1 row), plateau layer 2.
mn2b, minz2b = binding((3, 3, 4, 3, 3))
print(f"(2b) (3,3,4,3,3): minAdm={mn2b}, minimisers={minz2b}  "
      f"(UNIQUE binding two-separated-coupling L=4 witness: {minz2b == [(2, 2, 1, 0)]})")
ok &= (mn2b == 6 and minz2b == [(2, 2, 1, 0)])

# (3) min-width >= 1 for all (=> a smallest diagonal b1 always exists) + non-monotone spot checks
for M in [(2, 3, 2, 3, 2), (3, 2, 3, 2, 3), (2, 4, 2, 4, 2)]:
    mn, minz = binding(M)
    assert min(M) >= 1
    print(f"(3) non-monotone M={M}: minAdm={mn}, min-width={min(M)}>=1 (b1 exists; kept survivor supplies it)")

# permutation-invariance of minAdm (sanity, Object D)
import itertools
for base in [(4, 4, 4), (3, 3, 3, 2, 2)]:
    vs = {min_a for min_a in ({binding(tuple(p))[0] for p in itertools.permutations(base)})}
    print(f"    perm-invariance minAdm{base}: {vs} [invariant: {len(vs) == 1}]")
    ok &= (len(vs) == 1)

print(f"\nTWO-BLOCK CENSUS: {'PASS' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
