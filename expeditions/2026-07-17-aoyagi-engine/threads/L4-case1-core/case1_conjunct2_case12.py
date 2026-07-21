#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). Conjunct-2 (child Deg1SupportedOn) gate for the
# δ=1 case1(2) SPLIT edge — the controller-commissioned "before proof investment" verification.
"""
CONJUNCT-2 GATE for `case1_preserves_stepInv`'s δ=1 case1(2) branch.

The leaf must produce `∃ C', FoldStepInvAt d e C' (p.extend ed)`, whose conjunct-2 is
`Deg1SupportedOn (foldResid (p.extend ed)) C' univ`: EVERY child residual entry is a
CENTER-EXACT degree-1 form `∑_{i∈C'} c_i·u_i` (no degree-0 UNIT term, no degree-≥2 term).

The fold's `foldResid` at a δ=1 NON-terminal step is the STRICT TRANSFORM
    child_j(u) = foldResid_parent_j( k ↦ blockBlowupCoordQuot pivot k (sh u) )
with `blockBlowupCoordQuot pivot k = (1 if k==pivot else (sh u)_k)`. Since `pivot ∈ center`
(hpivot) and the parent is degree-1 on the center, the pivot's degree-1 term
`c_pivot·u_pivot` maps to `c_pivot(sh u)·1` — a UNIT unless `c_pivot ≡ 0`.

CONTROLLER'S QUESTION: is the case1(2) split pivot "always exceptional (not a parent residual
entry)" — i.e. is the cleared-pivot child entry always degree-1, never a bare unit?

We model the paper construction's residual FAITHFULLY (matrix-product fibre equations, the
blow-up + strict transform of the pnp thread-34 witnesses) and check the child residual's
degree structure ENTRY BY ENTRY, EXACTLY (sympy over Q), at:
  (I)  S < L  (interior layer): (3,3,2,2) at S=2, deep layer C3 pending.
  (II) S = L  (last layer):     (3,3,4)   at S=2, and (3,3,2,2) at S=3.

VERDICT LOGIC:
  * every child entry degree-1 on some center  ⟹ conjunct-2 HOLDS at that edge.
  * any child entry a bare UNIT (nonzero const term, no variable factor) ⟹ conjunct-2 FAILS
    (Deg1SupportedOn is false — the terminal_deg1_gap kernel: 1 ≠ ∑ c_i·u_i).

Then the GUARD CHECK: does the fold's terminal guard `nextState.layer < N` EXCLUDE the failing
edge? case1(2) keeps `layer` fixed; at S=L the Lean layer is N-1 < N, so the guard is TRUE
(edge NOT excluded) — the leaf's non-terminal branch must handle it.
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

def is_deg1_on(expr, center, allgens):
    """TRUE iff `expr` is CENTER-EXACT degree-1 on `center` (the `Deg1SupportedOn` condition for
    one entry / one candidate center): expr = ∑_{i∈center} c_i·u_i with c_i a polynomial in the
    NON-center coords. Equivalently: expr is HOMOGENEOUS of degree exactly 1 in the center
    variables jointly. Test by scaling center vars by λ and checking expr = λ·expr|_{λ=1}, i.e.
    the λ-polynomial of expr has ONLY the λ^1 term (no λ^0 UNIT term, no λ^≥2 term)."""
    lam = sp.Symbol('_lam')
    scaled = sp.expand(expr.subs({u: lam * u for u in center}))
    p = sp.Poly(scaled, lam)
    degs = set(p.monoms())          # each monom is a 1-tuple (power of λ)
    powers = {m[0] for m in degs}
    return powers <= {1}            # only λ^1 allowed (λ^0 = unit term ⟹ False)

def unit_term_on(expr, center):
    """The λ^0 (center-degree-0 / UNIT) part: expr with all center vars → 0. Nonzero ⟹ a unit
    term no center can support (the terminal_deg1_gap kernel: 1 ≠ ∑_{i∈C'} c_i·u_i)."""
    return sp.expand(expr.subs({u: 0 for u in center}))

def child_residual_is_deg1(child_entries, center, allgens, label):
    """Deg1SupportedOn on the candidate `center` holds iff EVERY entry is center-exact degree-1.
    Report the failing entries and whether the failure is a UNIT term (no center saves it)."""
    per = [is_deg1_on(x, center, allgens) for x in child_entries]
    units = [i for i, x in enumerate(child_entries) if unit_term_on(x, center) != 0]
    holds = all(per)
    print(f"    {label}: center C'={sorted(map(str,center))}")
    print(f"      per-entry deg1-on-C': {per}")
    if units:
        print(f"      -> entries {units} carry a nonzero UNIT term (const at C'=0) — "
              f"NO center C' can support them")
    return holds, bool(units)

# =====================================================================
# (I) S < L : (3,3,2,2) at S=2 (deep layer C3 pending). Expect child deg1 (Deg1 HOLDS).
# =====================================================================
print("=== (I) S<L: (3,3,2,2) S=2, case1(2) — deep layer C3 absorbs the cleared '1' ===")
r, s, t = sp.symbols('r s t')                 # layer-1 exceptionals
w = sp.symbols('w')                           # the case1(2) fresh exceptional (pivot axis)
C3 = sp.Matrix(2, 2, lambda i, j: sp.Symbol(f'c{i+1}{j+1}'))   # deep layer, pending
D1 = sp.Matrix(2, 1, lambda i, j: sp.Symbol(f'f{i+1}'))        # reduced residual after Schur step
# child fibre matrix = diag(b') · [[1,0],[0,D1_0],[0,D1_1]] · C3  (thread-34 deeplayer witness).
# The RESIDUAL family = the entries divided by the dominant b1' = r·w (strip the pure-exceptional b).
bp = [r * w, r * w * s, r * w * s * t]
red = sp.Matrix([[1, 0], [0, D1[0, 0]], [0, D1[1, 0]]])
Nchild = sp.diag(*bp) * (red * C3)            # 3×2 child fibre equations
resid_child_I = [sp.cancel(Nchild[i, j] / bp[0]) for i in range(3) for j in range(2)]
gens_I = [s, t] + list(C3.free_symbols) + list(D1.free_symbols)  # u-coords (NOT r,w: those are in b)
# candidate child center C' = the DEEP pending layer coords {C3} (NOT "C.erase pivot": the cleared
# pivot's row re-factors onto the DEEPER block, which absorbs the '1').
center_I = list(C3.free_symbols)
holds_I, units_I = child_residual_is_deg1(resid_child_I, center_I, gens_I, "(3,3,2,2) S=2 child residual")
check("(I) S<L child residual is degree-1 on C'={deep layer} (no unit) — conjunct-2 HOLDS", holds_I)
check("(I) S<L: no cleared-pivot UNIT term (deep layer absorbs the '1')", not units_I)

# =====================================================================
# (II) S = L : (3,3,4) at S=2, and (3,3,2,2) at S=3 — no deeper layer to absorb the '1'.
# =====================================================================
print("\n=== (II) S=L: (3,3,4) S=2, case1(2) — cleared pivot is a BARE UNIT (no deep layer) ===")
# thread-34 case1_witness_334 C12: row-1 child residual = (1, d12', d13', d14').
d12p, d13p, d14p = sp.symbols('d12p d13p d14p')
# child residual family (row 1; the cleared pivot entry is the bare '1'). Best-case child center
# C' = C.erase(pivot) = the other row-1 residual coords {d12',d13',d14'} (the controller's anchor-v).
resid_child_IIa = [sp.Integer(1), d12p, d13p, d14p]
gens_IIa = [d12p, d13p, d14p]
center_IIa = [d12p, d13p, d14p]
holds_IIa, units_IIa = child_residual_is_deg1(resid_child_IIa, center_IIa, gens_IIa,
                                              "(3,3,4) S=2 child residual row-1")
check("(IIa) S=L (3,3,4): cleared-pivot child entry is a bare UNIT — conjunct-2 FAILS", not holds_IIa)
check("(IIa) S=L: the failure IS a unit term (no center C' can rescue it)", units_IIa)

print("\n=== (II) S=L: (3,3,2,2) at S=3 (C3 consumed to diagonal) — bare unit appears ===")
g1, g2 = sp.symbols('g1 g2')
# at S=3=L the deep layer is resolved to a diagonal; cleared-pivot row = b1'·1 (bare).
resid_child_IIb = [sp.Integer(1), g1, g2]
gens_IIb = [g1, g2]
center_IIb = [g1, g2]
holds_IIb, units_IIb = child_residual_is_deg1(resid_child_IIb, center_IIb, gens_IIb,
                                              "(3,3,2,2) S=3 child residual")
check("(IIb) S=L (3,3,2,2): cleared-pivot child entry is a bare UNIT — conjunct-2 FAILS", not holds_IIb)
check("(IIb) S=L: the failure IS a unit term (no center C' can rescue it)", units_IIb)

# =====================================================================
# (III) GUARD CHECK: does `nextState.layer < N` exclude the failing S=L edge?
# =====================================================================
print("\n=== (III) does fix-(a)'s guard `nextState.layer < N` exclude the S=L case1(2) edge? ===")
# case1(2) keeps `layer` fixed (only rollover advances it). At the last layer S=L=N, the
# 0-indexed Lean layer is N-1. The child nextState.layer = N-1. Guard `nextState.layer < N`:
def guard_excludes_SL(N):
    layer_at_last = N - 1        # Lean 0-indexed layer for paper S = L = N
    nextlayer = layer_at_last    # case1(2) does NOT advance the layer
    return not (nextlayer < N)   # excluded iff guard is FALSE
for N in (2, 3, 4):
    excl = guard_excludes_SL(N)
    print(f"    N={N}: S=L case1(2) nextState.layer={N-1} < N={N} is {N-1 < N}"
          f"  ⟹ guard EXCLUDES the edge: {excl}")
guard_gap = all(not guard_excludes_SL(N) for N in (2, 3, 4))
check("(III) guard `nextState.layer < N` does NOT exclude any S=L case1(2) edge (GUARD GAP)",
      guard_gap)

print(f"\nCONJUNCT-2 case1(2) gate: interior-holds={holds_I} (unit-free={not units_I}), "
      f"S=L-fails={(not holds_IIa) and (not holds_IIb)} (unit-driven={units_IIa and units_IIb}), "
      f"guard-gap={guard_gap}")
# The battery PASSES (exit 0) when it correctly detects: interior OK, S=L broken, guard gap present.
# A passing battery is the WITNESS for a SECOND stop-on-suspect (the S=L case1(2) defect), NOT a GO.
print(f"\ncase1(2) conjunct-2 verdict battery: {'PASS (defect detected)' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
