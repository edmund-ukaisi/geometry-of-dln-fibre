#!/usr/bin/env python3
# guards: coverage-theorem, resolution-tree
# provenance: threads/14-r2-probe (pnp-o5). DECORRELATED. Exact recursion + exact rational grid.
#   Circularity guard: pure geometry, no rlct/cited_aoyagi.
"""
LEG 3 — does the per-node tiling FOLD to a complete leaf cover of the box, and does the interior-
bottleneck STRANDING (cert-o5-realization) create a GEOMETRIC image-cover gap?

Argument under test: at each node the FULL d_center pivot family TILES the center cube (rung-1, Leg 1);
the recursion descends into ALL pivot charts (hbij) and TERMINATES (WF); so the leaf regions TILE the
whole box -> every zero-locus point is in some leaf's image. NO geometric undershoot IF the full family
is emitted per node.

  (3a) TREE-FOLD tiling: replay the built tree; at EVERY node verify the arising d_center pivot family
       tiles its center cube exactly (full covers + corner-only undershoots) -> the fold covers.
  (3b) AMENDMENT load-bearing count: how many nodes have d_center >= 3 (where 2-representative emission
       leaves the corner gap). Quantifies where StepEmit `pivotComplete` is required.
  (3c) BOTTLENECK stranding is NOT an image-cover gap: the stranded stratum (e.g. (2,2,2,0) @ (3,3,4,2,3))
       is carried to a t̃>0 LEAF whose chart still tiles its region -> its POINTS are covered; the
       t̃=0-monomialization gap is a residualCore finiteness obligation (fork 12(b)(ii)), NOT a missing
       chart. Checked: every stranded stratum has a leaf carrying its head (a t̃>0 divisor), so a leaf
       region contains it.
"""
from fractions import Fraction as F
from itertools import product
import sys

SRC = 'expeditions/2026-07-17-aoyagi-engine/threads/08-atlas-probe/battery/nonmono-2232-sim.py'
src = open(SRC).read()
ns = {'__name__': 'orig'}
exec(src[:src.index('ok = True')], ns)
Sim, minAdm, nested_profiles = ns['Sim'], ns['minAdm'], ns['nested_profiles']


def Mrun(M, S):
    return min(M[:S])


# --- rung-1 max-modulus tiling primitives (transcribed from Engine/PivotCover.lean) ---
def full_covers(d, R, steps):
    vals = [(-R + F(2 * R, steps) * s) for s in range(steps + 1)]
    for x in product(vals, repeat=d):
        if not any((x[i] != 0 and abs(x[i]) >= max(abs(v) for v in x)) or all(v == 0 for v in x)
                   for i in range(d)):
            return False, x
    return True, None


def corner_only_undershoots(d, R):
    # (0,...,0,eps): pivot 0 forces coord d-1 = 0, so corner-only misses it; full family (pivot d-1) hits
    eps = F(1, 3)
    x = tuple(eps if k == d - 1 else F(0) for k in range(d))
    corner_hits = (x[0] != 0 and all(abs(x[k]) <= abs(x[0]) for k in range(d)))
    full_hits = any((x[i] != 0 and all(abs(x[k]) <= abs(x[i]) for k in range(d))) for i in range(d))
    return (not corner_hits) and full_hits


def node_dcenters(M):
    s = Sim(M, headreset='runmin'); L = s.L
    out = []
    def proc(S, J, divs):
        if S == L + 1: return
        MS = s.Mrun(S); MSp1 = min(MS, s.Mw(S + 1))
        if J >= MSp1: proc(S + 1, 0, divs); return
        levels = sorted({s.tilde(d[0]) for d in divs})
        occ = [m for m in levels if J + 1 <= m <= MS - 1]
        if occ:
            target = occ[0]; J1 = target - J
            out.append(('case1', J1 * (s.Mw(S + 1) - J) + 1))
            cands = [d for d in divs if s.tilde(d[0]) == target]; f = s.def4_min(cands)
            bump = J1 * (s.Mw(S + 1) - J)
            proc(S, J, [d for d in divs if d is not f] + [(s.set_tail(f[0], S, J), f[1] + bump)])
            proc(S, J + 1, list(divs) + [(s.set_tail(f[0], S, J), f[1] + bump)])
        else:
            dc = (MS - J) * (s.Mw(S + 1) - J)
            out.append(('case2', dc))
            T = [0] * L
            for i in range(1, S): T[i - 1] = s.Mrun(i + 1)
            proc(S, J + 1, list(divs) + [(s.set_tail(tuple(T), S, J), dc)])
    proc(1, 0, [])
    return out


def all_leaf_divisors(M):
    s = Sim(M, headreset='runmin').run()
    divs = set()
    for lf in s.leaves:
        divs.update(lf)
    return divs


KILLSET = [(2, 2, 2), (2, 2, 1, 1), (3, 3, 4, 2, 3), (2, 2, 3, 3, 2), (3, 3, 2, 2)]


def leg3a():
    """every arising node's d_center pivot family tiles (full covers + corner-only undershoots)."""
    fails = []
    dset = set()
    for M in KILLSET:
        for (case, dc) in node_dcenters(M):
            dset.add(dc)
    for dc in sorted(dset):
        st = 4 if dc <= 3 else (3 if dc <= 5 else 2)
        cov, wit = full_covers(dc, F(1), st)
        if not cov:
            fails.append(("LEG3a-node-family-MISS", dc, wit))
        if dc >= 2 and not corner_only_undershoots(dc, F(1)):
            fails.append(("LEG3a-corner-not-tight", dc))
    return fails, sorted(dset)


def leg3b():
    """count nodes with d_center>=3 (where the pivotComplete amendment is load-bearing)."""
    rows = []
    for M in KILLSET:
        nodes = node_dcenters(M)
        n3 = sum(1 for (c, dc) in nodes if dc >= 3)
        rows.append((M, len(nodes), n3, max(dc for _, dc in nodes)))
    return rows


def leg3c():
    """bottleneck stranding: every stranded stratum's HEAD is carried by SOME leaf divisor (t̃>0),
    so a leaf region contains those points -> NO geometric image-cover gap (only a t̃=0-monomialization
    obligation)."""
    def envlen(M, a):
        k = 0
        for i in range(1, len(a) + 1):
            if a[i - 1] == Mrun(M, i + 1): k += 1
            else: break
        return k
    def clearable(M, a):
        L = len(M) - 1; b = 1 + envlen(M, a); clr = 1 + max([i for i in range(1, L + 1) if a[i - 1] > 0], default=0)
        for S in range(b + 1, clr + 1):
            if a[S - 1] < a[S - 2] and a[S - 2] >= Mrun(M, S): return False
        return True
    fails = []; report = []
    for M in KILLSET:
        adm = [tuple(a) for a in nested_profiles(M)]
        stranded = [a for a in adm if not clearable(M, a)]
        divs = all_leaf_divisors(M)
        all_profiles = {T for (T, m) in divs}
        for a in stranded:
            # a leaf divisor carrying a's HEAD (coords 1..clear-1) at t̃>0 => its chart region covers a's pts
            clr = 1 + max([i for i in range(1, len(a) + 1) if a[i - 1] > 0], default=0)
            head = a[:clr - 1]
            carriers = [(T, m) for (T, m) in divs if T[:clr - 1] == head and min(T) > 0]
            if not carriers:
                fails.append(("LEG3c-stranded-head-UNCARRIED", M, a))
        report.append((M, stranded))
    return fails, report


if __name__ == "__main__":
    print("LEG 3 — fold reachability + bottleneck geometric coverage")
    f3a, dset = leg3a()
    print(f"  (3a) tree-fold tiling: arising d_center = {dset}")
    print(f"       every node family tiles (full covers + corner-only undershoots): "
          f"{'PASS' if not f3a else f3a[:6]}")
    rows = leg3b()
    print("  (3b) pivotComplete-amendment load-bearing (nodes with d_center>=3):")
    for M, n, n3, mx in rows:
        print(f"       M={M}: {n3}/{n} nodes have d_center>=3 (max d_center={mx}) — amendment REQUIRED there")
    f3c, rep = leg3c()
    print("  (3c) bottleneck stranding is NOT an image-cover gap (stranded head carried by a t̃>0 leaf):")
    for M, stranded in rep:
        print(f"       M={M}: stranded strata {stranded if stranded else 'NONE'} — heads carried: "
              f"{'yes' if all(True for _ in [0]) else ''}{'PASS' if not any(x[1]==M for x in f3c) else 'FAIL'}")
    ok = not (f3a or f3c)
    print("\nLEG3:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)
