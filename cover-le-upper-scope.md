# VERIFY-FIRST SCOPE — `cover_le` UPPER leg (the cover-completeness / finiteness transfer)

Read-only scope before deep-fill (genm-p44c). Verdict: **BOUNDED, no new math, but a genuine
recursive-carrier build — NOT a quick fill.** The "no missing strata" completeness IS the documented
`RouteMRecursion` branch-`sorry` (the fixed-arity carrier's recursion), needing ~3 Core-level pieces;
proven sorry-free on 3 anchors ((2,2,2),(3,3,4),(4,4,2,2)), so the SHAPE is validated, not speculative.

## Exact reduction (the induction shape)

`IsRouteMCover.cover_le` (RouteMBridge:63): `∀c', ∃C<⊤, ∫⁻_U |F|^{−c'} ≤ C·Σ_leaves ∫_box monomial`.
Reduces via the BANKED abstract reducer `routeM_coverLe_of_finiteness` (RouteMCoverLemmas:44) to TWO
general-M facts:
- **hpos**: leaf-sum RHS `≠ 0` — **BANKED general-M** (RouteMLayerCover, off `monomialIntegrand_pos_on_interior`).
- **hfin**: the FINITENESS TRANSFER — `(leaf-sum < ⊤) ⟹ ∫_U |F|^{−c'} < ⊤`. **This is the genuine residual.**

`hfin` = the change-of-variables/cover bound `∫_{routeMBaseNbhd M} |routeMCore M|^{−c'} ≤
routeMLayerBoxIntegral M c'` (RouteMBoxReduction's box-reduction `…_le`). Its content: the recursive
pivot-blowup charts COVER the base box `(−1,1)^N` up to a null set ("no missing strata"), and on each
chart the c-o-v turns `|routeMCore|^{−c'}` into the leaf monomial integrand. This is the cover-COMPLETENESS.

## What's BANKED toward hfin (the SHAPE is proven)

- **3 per-M anchors, SORRY-FREE**: `routeMCore_M4422_*` (4,4,2,2), `routeMCore_M334_*` (3,3,4),
  `myF222_*` / `routeM222_below_threshold_fin` (2,2,2). Each: iterate `recStep` (pivot-blowup split) →
  per-summand finiteness → the box bound. So the per-chart c-o-v + per-summand finiteness machinery is
  BUILT and validated on both ends of the family.
- The box-reduction `RouteMBoxReduction` (`∫_baseNbhd ≤ routeMLayerBoxIntegral`) + the depth-2 (3,3,4)
  recStep weld (#95-98) — the recursive descent infrastructure.

## The genuine open piece (the induction, BOUNDED but multi-tide)

The general-M `hfin` rides the **`RouteMRecursion.RouteMState` recursion**, whose `branch` arm is the
**documented `sorry`** (RouteMRecursion:155-172): a `branch` cell = a `Finset` of pivot choices, each a
`ChainDimSplit M` whose `red` is `chainRel`-below `M` (the descent). The branch-recursion's certified
body needs "three Core-level pieces" (per the in-file note; the alternatives were judged worse, so it's
left named). This recursion IS the "no missing strata" completeness: proving the recursively-generated
pivot charts cover the box up to null, by induction on the `chainRel`-descent, the `⨅`-min over branches.

VERDICT per the gate:
- **NOT new math / NOT a wall**: no false statement, no counterexample; the shape is proven sorry-free on
  3 anchors; the obstruction is the recursive-carrier transcription (the `branch` arm + 3 Core pieces),
  a packaging/induction gap. Bounded.
- **NOT a quick fill**: it's the fixed-arity-carrier `branch` recursion — a genuine multi-tide build
  (the recursion + the 3 Core-level pieces + the null-cover completeness lemma). The "bounded-harder" of
  my R1-map's two atoms, confirmed.
- **Independent of |det Dφ|** (genm-eineout's lane): hfin is the UPPER/finiteness leg; it uses the
  per-chart c-o-v's monomial form, NOT the divergence Jacobian's sharp exponent. Non-colliding. ✓

## Recommended build sequence (for the deep-fill, if green-lit)

1. SPECIFY the general `hfin` (the box-reduction at general M) + the `branch`-recursion completeness
   lemma signatures; validate they typecheck against the 3 anchors' shape.
2. The recursion: `RouteMState`-branch cover-completeness by `chainRel`-descent induction (the documented
   3 Core pieces — pin each as its own clean-three sub-lemma).
3. Wire general `hfin` → `routeM_coverLe_of_finiteness` → `cover_le` (general M).
The anchors give the base + a 2-level worked case; the multi-tide is the ∀-descent recursion.

Read-only; no .lean writes. Refs: RouteMBridge:63 (cover_le), RouteMCoverLemmas:44 (reducer),
RouteMBoxReduction (box-bound), RouteMRecursion:155 (the branch sorry), anchors RouteM{222,334,4422}*.
