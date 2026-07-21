#!/usr/bin/env python3
"""
Thread-41 (Object-E ρ count-object) adjudication battery. EXACT integer/Fraction arithmetic.

PINS the count-object behind Aoyagi's pole multiplicity ρ (paper's θ in Lemmas 4-5; worked.tex:216
ρ = max_u #{j : (h_j+1)/(2k_j)=λ}) and VERIFIES ρ = a(ℓ−a)+1 EXACTLY over the resolution tree/atlas.

CLAIM (elder hypothesis, adjudicated): ρ = MAX-CROSSING NUMBER
  = max over leaves (charts) of #{binding divisors co-crossing at the deepest point of that chart}
  = max over leaves of #{divisors u_{s,k} in the leaf with t̃=0 AND Mval=minAdm}.
(Within a normal-crossing chart all binding coordinate-divisors {u=0} pass through the chart origin =
the deepest point, so the per-chart max-crossing = the per-chart binding-divisor count.)

CONTRAST: naive := #{distinct admissible minimising profiles t : Mval(t)=minAdm} — OVERCOUNTS ρ, because
minimising profiles are split across DIFFERENT leaves; no single chart need contain all of them.
"""
import sys, os, importlib.util
from fractions import Fraction
from itertools import product as iproduct

EDGE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                    "edgespec_traversal_334.py")
if not os.path.exists(EDGE):
    EDGE = "/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/expeditions/2026-07-17-aoyagi-engine/threads/37-paper-mining/edgespec_traversal_334.py"
spec = importlib.util.spec_from_file_location("edge334", EDGE)
edge = importlib.util.module_from_spec(spec); spec.loader.exec_module(edge)   # safe: __main__ guarded

ok = True
def check(name, cond):
    global ok
    c = bool(cond); ok &= c
    print(f"  [{'PASS' if c else 'FAIL'}] {name}")

# ---------- admissible profile lattice + Mval ----------
# Proper nested-rank bound: prof[i] = t^(i+1) is a rank, bounded by the RUNNING-MIN width min(M^1..M^{i+2}).
# (The loose min(M0,M1) cap admits degenerate profiles like (4,2,0) with t^(2)=2 > M^(3)=1, giving a
#  spurious Mval=0 — corrected here.)
def adm_profiles(M):
    L = len(M)-1
    caps = [min(M[:i+2]) for i in range(L)]     # cap for t^(i+1): running min of M^1..M^{i+2}
    for prof in iproduct(*[range(0, caps[i]+1) for i in range(L)]):
        if prof[-1] == 0 and all(prof[i] >= prof[i+1] for i in range(L-1)):
            yield prof
def minAdm_lattice(M):
    return min(edge.mval(M, p) for p in adm_profiles(M))
def minAdm_tree(M):
    """The GEOMETRIC minimum: min over all leaves, over t̃=0 divisors, of exp (real profiles only)."""
    best = None
    for lf in tree_leaves(M):
        for (prof, exp) in lf["divs"]:
            if min(prof) == 0:
                best = exp if best is None else min(best, exp)
    return best

# ---------- Def-3 (a, ℓ): the ℓ+1 smallest reduced widths participate (max-ℓ, worked.tex ≥-fix) ----------
def def3_a_ell(M):
    w = sorted(M); n = len(w)
    best_m = 2
    for m in range(2, n+1):                 # |ℳ| = m, ℓ = m-1
        P = sum(w[:m]); ell = m-1
        if w[m-1]*ell < P:                  # each member < balanced average P/ℓ
            best_m = m
    m = best_m; ell = m-1; P = sum(w[:m])
    Mstar = -(-P // ell)                    # ceil(P/ℓ); M*-1 < P/ℓ ≤ M*
    a = P - (Mstar-1)*ell                   # 1 ≤ a ≤ ℓ, P = ℓ(M*-1)+a
    return a, ell, P, Mstar
def aoyagi_rho(M):
    a, ell, _, _ = def3_a_ell(M)
    return a*(ell-a) + 1

# ---------- the resolution tree: per-leaf binding-divisor sets (memoised) ----------
_LEAF_CACHE = {}
def tree_leaves(M):
    key = tuple(M)
    if key not in _LEAF_CACHE:
        edge.EDGES = []
        root = edge.State(0, 0, [])
        tree = edge.build(M, root, [])
        leaves = []; edge.collect_leaves(tree, leaves)
        _LEAF_CACHE[key] = leaves
    return _LEAF_CACHE[key]
def rho_maxcross(M):
    """ρ = max over leaves of #{binding divisors (t̃=0, exp=minAdm) co-crossing at that chart's origin}."""
    mA = minAdm_tree(M)
    best = 0; witness = None
    for lf in tree_leaves(M):
        binding = [(prof, exp) for (prof, exp) in lf["divs"] if min(prof) == 0 and exp == mA]
        if len(binding) > best:
            best = len(binding); witness = binding
    return best, mA, witness
def naive_count(M):
    """Total distinct minimising profiles over the CORRECT (running-min rank-bounded) lattice."""
    mA = minAdm_tree(M)
    return sum(1 for p in adm_profiles(M) if edge.mval(M, p) == mA)
def adm_profiles_loose(M):
    """seat-E's / edgespec's LOOSE lattice (cap = min(M^1,M^2) for every t^(j)) — admits degenerate
    profiles (rank exceeding a later width). Reproduces the 'naive=2 at [3,3,1,1]' artifact."""
    L = len(M)-1
    rng = range(0, min(M[0], M[1])+1)
    for prof in iproduct(*[rng]*L):
        if prof[-1] == 0 and all(prof[i] >= prof[i+1] for i in range(L-1)):
            yield prof
def naive_loose(M):
    mA = min(edge.mval(M, p) for p in adm_profiles_loose(M))
    return sum(1 for p in adm_profiles_loose(M) if edge.mval(M, p) == mA), mA

# ================= CHECK 0: Def-3 (a,ℓ) reproduces hand-computed values =================
print("=== CHECK 0: Def-3 (a,ℓ) selection vs hand values ===")
for M, exp_a, exp_l in [([2,2,2],2,2), ([2,2,2,2],2,3), ([3,3,4],2,2), ([2,1,2],1,2), ([3,3,1,1],1,1)]:
    a, l, P, Ms = def3_a_ell(M)
    check(f"M={M}: (a,ℓ)=({a},{l}) == expected ({exp_a},{exp_l})", a == exp_a and l == exp_l)

# ================= CHECK 1: ρ_maxcross == a(ℓ−a)+1 == known ground truth =================
print("\n=== CHECK 1: ρ = max-crossing = a(ℓ−a)+1, on the tree-ρ ground truths ===")
GROUND = {(2,2,2):1, (3,3,4):1, (2,2,3,2):1, (2,2,2,2):3, (2,1,2):2}
for Mt, rho_known in GROUND.items():
    M = list(Mt)
    rho_mc, mA, wit = rho_maxcross(M)
    rho_f = aoyagi_rho(M)
    nv = naive_count(M)
    a, l, _, _ = def3_a_ell(M)
    print(f"  M={M}: minAdm={mA}  max-crossing ρ={rho_mc}  a(ℓ−a)+1={rho_f} (a={a},ℓ={l})  "
          f"naive={nv}  known ρ={rho_known}")
    check(f"M={M}: max-crossing == a(ℓ−a)+1 == known ρ ({rho_known})",
          rho_mc == rho_f == rho_known)

# ================= CHECK 2: the naive count DIVERGES; ρ tracks max-crossing, not naive =================
print("\n=== CHECK 2: wide scan — max-crossing==a(ℓ−a)+1 everywhere; loose-naive divergence reproduced ===")
loose_div = []      # loose-naive ≠ formula  (seat-E's artifact class)
tight_div = []      # tight-naive ≠ max-crossing  (a GENUINE divergence, if any)
formula_mismatch = []
minadm_mismatch = []
scanned = 0
seen = set()
for L in (2, 3, 4):
    hi = 5 if L <= 3 else 3
    for widths in iproduct(range(1, hi+1), repeat=L+1):
        M = list(widths)
        key = tuple(M)
        if key in seen: continue
        seen.add(key)
        scanned += 1
        rho_mc, mA, wit = rho_maxcross(M)
        rho_f = aoyagi_rho(M)
        nv_t = naive_count(M)
        nv_l, mA_l = naive_loose(M)
        if minAdm_tree(M) != minAdm_lattice(M):
            minadm_mismatch.append((M, minAdm_tree(M), minAdm_lattice(M)))
        if rho_mc != rho_f:
            formula_mismatch.append((M, rho_mc, rho_f))
        if nv_l != rho_f:
            loose_div.append((M, nv_l, rho_f))
        if nv_t != rho_mc:
            tight_div.append((M, nv_t, rho_mc, rho_f))
print(f"  scanned {scanned} distinct cores (L∈{{2,3,4}}).")
print(f"  minAdm tree-vs-lattice mismatches: {len(minadm_mismatch)}")
print(f"  FORMULA mismatches (max-crossing ≠ a(ℓ−a)+1): {len(formula_mismatch)}")
print(f"  LOOSE-naive divergences (seat-E artifact class, degenerate profiles counted): {len(loose_div)}")
for (M, nv, rf) in loose_div[:8]:
    print(f"    loose: M={M}: loose-naive={nv}  a(ℓ−a)+1=ρ={rf}   (degenerate-profile OVERCOUNT)")
print(f"  TIGHT-naive vs max-crossing GENUINE divergences: {len(tight_div)}")
for (M, nv, rmc, rf) in tight_div[:12]:
    print(f"    GENUINE: M={M}: tight-naive={nv}  max-crossing(ρ)={rmc}  a(ℓ−a)+1={rf}")
check("max-crossing == a(ℓ−a)+1 for EVERY scanned core (no formula mismatch)", len(formula_mismatch) == 0)
check("minAdm_tree == minAdm_lattice for every scanned core (rank-bounded lattice validated)",
      len(minadm_mismatch) == 0)
check("loose-naive DIVERGES from ρ (reproduces seat-E's artifact: degenerate profiles overcount)",
      len(loose_div) > 0)
check("[3,3,1,1] is a loose-naive divergence (loose-naive=2, ρ=1) — seat-E's lead witness reproduced",
      any(M == [3,3,1,1] and nv == 2 and rf == 1 for (M, nv, rf) in loose_div))

# ================= CHECK 3: BOTH DIRECTIONS of ρ = a(ℓ−a)+1 (bound + attainment), per instance =================
print("\n=== CHECK 3: exact ρ = a(ℓ−a)+1 both directions over the whole scan ===")
upper_ok = True; attain_ok = True
for L in (2, 3):
    for widths in iproduct(range(1, 5), repeat=L+1):
        M = list(widths)
        rho_mc, mA, wit = rho_maxcross(M)
        rho_f = aoyagi_rho(M)
        # UPPER: no leaf carries more than a(ℓ−a)+1 binding divisors
        if rho_mc > rho_f: upper_ok = False
        # ATTAINMENT: some leaf carries exactly a(ℓ−a)+1
        if rho_mc < rho_f: attain_ok = False
check("UPPER: every leaf has ≤ a(ℓ−a)+1 co-crossing binding divisors (max-crossing ≤ formula)", upper_ok)
check("ATTAINMENT: some leaf realises exactly a(ℓ−a)+1 (max-crossing ≥ formula)", attain_ok)

# ================= CHECK 4: the GENUINE-divergence witness [2,2,2,2,2], concretely =================
print("\n=== CHECK 4: the genuine (non-artifact) witness [2,2,2,2,2] — 6 valid minimisers, ρ=5 ===")
M = [2,2,2,2,2]
mA = minAdm_tree(M)
mins = sorted({p for p in adm_profiles(M) if edge.mval(M, p) == mA})
print(f"  minAdm={mA}; #valid minimising profiles (tight lattice) = {len(mins)}: {mins}")
# per-leaf binding sets; the max co-crossing leaf and the union
leafsets = []
for lf in tree_leaves(M):
    b = frozenset(prof for (prof, exp) in lf["divs"] if min(prof) == 0 and exp == mA)
    if b: leafsets.append(b)
union = frozenset().union(*leafsets) if leafsets else frozenset()
maxleaf = max(leafsets, key=len)
print(f"  max co-crossing leaf has {len(maxleaf)} binding divisors: {sorted(maxleaf)}")
print(f"  union of all leaves' binding divisors = {len(union)} profiles (= tight-naive if complete)")
missing_from_maxleaf = sorted(union - maxleaf)
print(f"  minimiser(s) NOT in the max leaf (live on other branches): {missing_from_maxleaf}")
check("[2,2,2,2,2]: 6 valid minimisers but max-crossing = 5 = a(ℓ−a)+1 (GENUINE incidence gap)",
      len(mins) == 6 and len(maxleaf) == 5 and aoyagi_rho(M) == 5)
check("[2,2,2,2,2]: the tree UNION of binding divisors = the full minimiser set (tree sees every minimiser)",
      union == frozenset(mins))

# ================= CHECK 5: tree-completeness + the t̃=0 (page-22 candidate) restriction is LOAD-BEARING =====
print("\n=== CHECK 5: ⋃_leaves(binding) == minimiser set; and the t̃=0 (page-22) restriction is load-bearing ===")
# Page 22: the RLCT candidates are ½·min{M_{s,k} : t̃_{s,k}=0} — ONLY t̃=0 (deepest-stratum) divisors are
# candidates. Non-terminal (t̃>0) divisors are NOT binding (they lie over shallower points; e.g. [2,2,5]
# has a t̃>0 divisor of exp 1 < minAdm 4 that is NOT the RLCT). So ρ counts t̃=0 binding divisors only.
complete_ok = True
loadbearing = []       # cores where dropping t̃=0 would OVERcount (proves the restriction matters)
notcand_below = []     # cores with a t̃>0 divisor whose exp < minAdm (a NON-candidate below the RLCT)
seen2 = set()
for L in (2, 3, 4):
    hi = 5 if L <= 3 else 3
    for widths in iproduct(range(1, hi+1), repeat=L+1):
        M = list(widths); key = tuple(M)
        if key in seen2: continue
        seen2.add(key)
        mA = minAdm_tree(M)                       # = min over t̃=0 divisors (page-22 candidate min)
        mins = {p for p in adm_profiles(M) if edge.mval(M, p) == mA}
        leaves = tree_leaves(M)
        union = set(); maxc = 0; maxc_all = 0
        has_below = False
        for lf in leaves:
            b = [prof for (prof, exp) in lf["divs"] if min(prof) == 0 and exp == mA]
            union |= set(b); maxc = max(maxc, len(b))
            maxc_all = max(maxc_all, sum(1 for (prof, exp) in lf["divs"] if exp == mA))  # drop t̃=0
            if any(exp < mA for (prof, exp) in lf["divs"] if min(prof) > 0):
                has_below = True
        if union != mins: complete_ok = False
        if maxc_all > aoyagi_rho(M): loadbearing.append((M, maxc, maxc_all, aoyagi_rho(M)))
        if has_below: notcand_below.append(M)
check("⋃_leaves(t̃=0 binding divisors) == full valid-minimiser set for EVERY scanned core (tree complete)",
      complete_ok)
check("the t̃=0 (page-22 candidate) restriction is LOAD-BEARING: without it the count EXCEEDS a(ℓ−a)+1",
      len(loadbearing) > 0)
print(f"  cores where dropping t̃=0 overcounts a(ℓ−a)+1: {len(loadbearing)} (e.g. {loadbearing[0][0] if loadbearing else '—'}: "
      f"t̃=0 count {loadbearing[0][1]} vs all-ratio-λ count {loadbearing[0][2]}, formula {loadbearing[0][3]})")
print(f"  cores with a t̃>0 divisor of exp < minAdm (a NON-candidate BELOW the RLCT, page-22-excluded): "
      f"{len(notcand_below)} (e.g. [2,2,5]: t̃>0 exp-1 divisor, minAdm=4 — NOT the RLCT)")
check("[2,2,5] has a t̃>0 exp<minAdm divisor that is correctly NOT the RLCT (page-22 t̃=0 candidate rule)",
      [2,2,5] in notcand_below)

print(f"\nTHREAD-41 ρ COUNT-OBJECT BATTERY: {'PASS (EXIT 0)' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
