# Thread 23 — per-pivot local-product atlas over the rank-=r open (B3-6/B3-7) (formaliser) — certificate

**Formaliser tide (bundle-conjugation).** New module `Core/FibreBundleLocallyTrivialFull.lean` (341
LoC), wired by the controller; whole library green (3804 jobs); headlines axiom-clean `[propext,
Classical.choice, Quot.sound]` (controller-gated); reviewer PASS-WITH-CONCERNS (actioned) + 4 decorrelated
Codex consults. Commits `65e02162` (B3-6), `2ec95a4f` + `f96a55fa` (B3-7).

## HEADLINE — a genuine coherent local-product ATLAS over the rank-=r open (honestly NOT `locallyTrivial`)
`reducedFibre_pivotLocalProductAtlasOnRankOpen` — the assembled `PivotLocalProductAtlas` with all fields
instantiated: scheme open-cover + per-pivot trivializations into the standard fibre `SchurLoc ⊗
sweepFibreRing` + the coherent base-side overlap cocycle + the intertwining. Named `…AtlasOnRankOpen`,
NOT `locallyTrivial` — that identifier was judged a mild overclaim (see below).

## Two framing corrections the tide made (decorrelated Codex ×3–4, both decisive)
1. **The controller's "identify with the AMBIENT `awayOverlapTransition`" steer was a RED HERRING.** The
   per-pivot charts are localizations of the BASE `sweepSigmaRing`; the genuine cocycle is
   `awayOverlapTransition (chartDsigAt I) (chartDsigAt J)` over `sweepSigmaRing` (thread-19 engine, laws
   inherited for free). The tide built the correct base-side object instead of the mis-aimed ambient one.
   The ambient cross-ring identification is exposition value only, NOT the bottleneck.
2. **A bare scheme-theoretic `locallyTrivial` over the CLOSURE `Σ̄^r` is FALSE.** `sweepSigmaRing =
   O(Σ̄^r)` is the closure's ring; rank-`<r` boundary points vanish ALL `r×r` minors ⟹ lie in NO chart.
   The charts cover exactly the OPEN rank-`=r` locus `Σ^r`. So `span{chartDsigAt} = ⊤` does NOT hold over
   the closure; the honest cover is over the rank-`=r` open.

## Landed (axiom-clean)
- `chartOverlapTransition` (+ `_commutes`/`_symm`/`_trans_symm`) — the base-side overlap cocycle over
  `sweepSigmaRing` (via `PivotDatum`/`pivotElt`).
- `chartLocalizedAlgEquivAt_transition_eq_gauge` — THE INTERTWINING: the transition `e_I ≪≫ e_J.symm`
  factors through the base gauges (`e_β` cancels), hence base-algebraic.
- `rankROpen := (V({chartDsigAt}))ᶜ` + `iSup_pivot_basicOpen_eq_rankROpen` — the scheme-level open-cover
  of the rank-`=r` open by the per-pivot charts.
- `sweepSigma_subset_chartOpen` — the POINT-SET cover of `Σ^r` (from `exists_invertible_minor_of_rank` +
  `eval_det_submatrix_multPoly`).
- `PivotLocalProductAtlas` (structure: cover + trivializations + cocycle + intertwining + schemeCover) +
  `pivotLocalProductAtlas` + the headline `reducedFibre_pivotLocalProductAtlasOnRankOpen`.

## NAMING (honest, reviewer + 4th Codex consult)
`locallyTrivial` dropped from the identifier: (i) `rankROpen` is DEFINED as the chart-cover-complement, so
`schemeCover` is near-definitional; (ii) `rankROpen = {rank=r}` is the geometric reading, NOT a formalized
scheme equality; (iii) a bare `locallyTrivial` over the closure is false. The structure name
`PivotLocalProductAtlas` carries the honest content.

## The ONE remaining rung to a bare `locallyTrivial` (#133r, small, no new math)
The Lean-formalized rank-tie `rankROpen = {rank=r}` — the converse of the banked forward inclusion
(`sweepSigma_subset_chartOpen`), a Nullstellensatz over the rank-`=r` open. ~150–300 LoC CA, NO new
mathematics (Codex). With it the headline could honestly carry `locallyTrivial`.

## Net B3 state
cover (#18) + ambient cocycle (#19) + top-left datum (#21) + per-pivot trivializations (#22) + the
coherent per-pivot atlas with base-side cocycle + scheme cover over the rank-=r open (#23). The bundle is
substantively a coherent local-product atlas; the rank-tie (#133r) is the small final step to the formal
`locallyTrivial` name.

## Artifacts (committed @ 65e02162 / 2ec95a4f / f96a55fa)
`threads/23-locally-trivial-full/statement-card.md` + 4 codex consults (cocycle, naming, reconcile,
review-honesty). Lean: `Core/FibreBundleLocallyTrivialFull.lean`.
