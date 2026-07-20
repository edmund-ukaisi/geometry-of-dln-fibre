# Fold-Jacobian SPECIFY — LeafJacobian's β-det over the geometric fold (for t11)

*Author: `coverage-t08`. The last authoring act; the SPECIFY handoff for the fold-Jacobian builder (t11,
the wall / L2-D1 class). Everything is banked: the per-blow-up det atoms, the q-det trio (t09), the fold
(`GeoChart.lean`), the ledger (`stepUpdate`). Statement + induction + substitution table + pins below;
t11 grinds the PROVE. Consistency check owed too (LeafPullback size-and-report, below).*

## The target (LeafJacobian's β-det, ledger-ACCUMULATED)

For each geometric atlas piece — i.e. each `(leaf, composite) ∈ geometricLeafPaths (dCenterOfNode M)
(qNodeOf M) id t` (the composite is the piece's `chartMap`) — the Fréchet-derivative determinant of the
composite is the ledger monomial:

    |det D(composite) w| = ∏ k : Fin leaf.numDiv, |paramsEquivFlat M w (leaf.divCoord k)| ^ (leaf.divExp k − 1)

with `leaf.divExp` the `stepUpdate`-ACCUMULATED exponent (NOT the per-single-blow-up `d−1`). This is
LeafJacobian's `Dβ` clause (`EngineDefs.lean:62-64`); the full `LeafJacobian c` then closes with `β :=
c.chartMap` (the composite), `ψ := id`, `ψsymm := id` (`|det Dψ| = 1`, bounded — R-b puts the gauge in
the SOURCE, absorbed into `β`; see §α below), `lo = hi = 1`. So the crux is this fold-det identity.

## Why the design note "both dets banked" was an undercount

The banked `abs_det_fderiv_pivotChart` gives the PER-SINGLE-BLOW-UP exponent `|z|^{d−1}`; the leaf needs
the SUM over the root→leaf path (a divisor's exponent grows as it is re-merged/re-blown-up). The missing
piece is the path-INDUCTION accumulating those per-edge contributions into `leaf.divExp k`. That is this
module.

## The induction skeleton (path fold + chain rule)

`composite = fold of the per-edge `β̃_e` down the root→leaf path` (`geometricLeafPaths`'s `acc`). Induct
on the path (tree structure, `Edge.mk` destructure, mirroring `imgAcc`/`leafPathImages`):

    |det D(composite)| = |det D(edge β̃)| · |det D(child composite)|        (chain rule, det multiplicative)

- **chain rule / det-multiplicativity**: `fderiv (g ∘ f) = (fderiv g) ∘ (fderiv f)` (`HasFDerivAt.comp`),
  `ContinuousLinearMap.det (A.comp B) = A.det · B.det` (Mathlib `ContinuousLinearMap.det_comp` /
  `LinearMap.det_comp`); `|·|` via `abs_mul`.
- **the edge β̃ det** = `|z_pivot|^{d_center_node − 1}` (single pivot), via:
  - q-CONJUGATION (t09's q-det trio): `β_e = (qOfCenter …).symm ∘ (Prod.map (pivotChart p) id) ∘ (qOfCenter …)`;
    `qOfCenter_hasFDerivAt` says `fderiv (qOfCenter …) x = qOfCenterCLE …` (a FIXED CLE), likewise
    `_symm_hasFDerivAt`. So `fderiv β_e w = CLE.symm ∘ D(pivotChart p ×ˢ id) ∘ CLE`, and
    `det = det(CLE.symm)·det(D pivotChart×id)·det(CLE) = det(D pivotChart×id)` (the CLE dets cancel —
    `det(CLE.symm) = det(CLE)⁻¹`; use `ContinuousLinearMap.det_comp` + the equiv-det inverse, or the
    banked "conjugation preserves det" shape).
  - `det(D(pivotChart p ×ˢ id)) = det(D pivotChart p) · det(D id) = |z_p|^{d_center−1} · 1`
    (`abs_det_fderiv_pivotChart` + the product/`Prod.map` fderiv-det = product of factor dets;
    `HasFDerivAt.prodMap`, `ContinuousLinearMap.det_prod`-style).
- **the α (R-b source gauge) det = 1**: `β̃_e = β_e ∘ α_e⁻¹`, `|det Dα_e| = 1`
  (`abs_det_fderiv_elemShear`; `α_u = refl`), so `|det Dβ̃_e| = |det Dβ_e|` — the gauge is det-neutral,
  it only reshapes the residual (LeafPullback), not the monomial Jacobian.

## The exponent accumulation — THE CRUX (elder's substitution table)

`∏_edges |z_pivot(edge)|^{d_center−1} = ∏_k |z_k|^{leaf.divExp k − 1}` requires tracking how each edge's
substitution moves coordinates so the per-edge contributions accumulate onto the RIGHT divisor's ledger
exponent. The elder's table (per edge):
- **case-1(1) u-chart** (`u ↦ u`, `d_a ↦ u·d'_a`): contributes `|u|^m` to the u-divisor; the residual
  `d`-entries carry `u` as a factor (inheritance).
- **case-1(2) / case-2 d_j-chart** (`u ↦ d_j·u'`, `d_a ↦ d_j·d'_a`): contributes `|d_j|^m` to the new
  pivot; **the inherited `M−1`** (the merged divisor's prior exponent) pulls through the substitution
  (the `d_j·u'` factor carries the old `u`'s power).
Per-case ledger derivations (tie the per-edge contribution to `stepUpdate`, `EngineDefs.lean:127-154`):
- **case11**: `divExp(mergeIdx) += runLen·resCols` — the u-divisor's exponent grows by the run.
- **case12**: new pivot `divExp = divExp(mergeIdx) + runLen·resCols` — the inherited base `+` the run.
- **case2**: new pivot `divExp = resRows·resCols`.
So `leaf.divExp k` = the accumulated sum, and the fold-det's per-edge product must reindex/telescope onto
it. **This telescoping is the wall** — the coordinate-tracking through the substitutions (which `z_k` each
edge's `|z_pivot|^{d−1}` lands on, and that the powers sum to `divExp k − 1`). Expect the L2/D1
`endpoint_telescoping`/`prodAux` reassociation idioms (`lean/CLAUDE.md` § dependent-dim reassociation).

## Consumed atoms (pinned)

- `abs_det_fderiv_pivotChart` (ShearReconcile) — `|det D(pivotChart i)| = |u_i|^{d−1}`.
- `abs_det_fderiv_elemShear` (ShearReconcile) — `|det Dα| = 1` (the source gauge, det-neutral).
- q-det trio (QNodeCarrier, t09): `qOfCenterCLE`, `qOfCenter_coe_cle` (rfl), `qOfCenter_hasFDerivAt` /
  `qOfCenter_symm_hasFDerivAt` (fderiv = the fixed CLE — the conjugation inputs). LINEARITY form (not MP);
  MP not needed (the det-conjugation is linear-algebraic). No MP flag.
- `geoChartMap` / `geometricLeafPaths` / `tGeo` (GeoChart; tGeo t10-built or reuse geometricLeafPaths) —
  the fold structure to induct on.
- `stepUpdate` / `divExp` (EngineDefs) — the ledger being matched.
- Mathlib: `ContinuousLinearMap.det_comp`, `HasFDerivAt.comp`, `HasFDerivAt.prodMap`, `abs_mul`, the
  `Finset.prod` telescoping/reindex lemmas.

## t11 brief items

- **LeafPullback SIZE-AND-REPORT** (you hold the same substitution table, so you're best placed): report
  LeafPullback's TRUE shape before anyone proves it. My check: its monomial is `∏ divCoord^2` (power-2
  UNIFORM, `EngineDefs.lean:47`), NOT the accumulated `∏ divCoord^{divExp−1}` — so it does NOT share this
  fold-induction. Its obligation: the loss `frobSq(prod M (composite w))` factors as `(∏ divCoord²)·core`
  with the ACCUMULATED extra divisor powers (>2, from the fold) absorbed into `residualCore` (the lo/hi
  squeeze against `residualBaseForm`). Size whether that absorption is (a) direct (the extra powers are a
  bounded positive factor on `srcBox`) or (b) needs its own accumulation lemma; report, don't commit.
- **Tripwire spots I foresee** (where the take-would-thrash risk concentrates): (1) the exponent
  telescoping/reindex — matching `∏_edges |z_pivot|^{d−1}` to `∏_k |z_k|^{divExp k − 1}` through the
  substitution coordinate-tracking (dependent-index reassociation, the L2/D1 idiom); (2) the CLE-det
  cancellation `det(CLE.symm)·det(CLE) = 1` in the conjugation (get the `ContinuousLinearMap.det` of an
  equiv + its inverse right — likely `LinearEquiv.det`/`ContinuousLinearEquiv` det API); (3) the
  `Prod.map` fderiv-det = product of factor dets (block-diagonal det — `det_prod`/`fromBlocks` shape);
  (4) the α-inheritance pull-through (case-1(2)'s `M−1` inherited base — the substitution `d_j·u'` carrying
  the old power). Consult Codex on (1) and (2) before grinding.

## Fill-target

If the statement states cleanly I'll add a `GeoJacobianSpec.lean` skeleton (the `∀ (lc) ∈ geometricLeafPaths …,
|det D lc.2| = ∏ |lc.1.divCoord|^{lc.1.divExp − 1}` statement + one tracked sorry, the GeoCoverSpec pattern);
otherwise this .md is the spec and t11 states it with its induction-motive design choices. (Attempting the
Lean statement now — see the companion commit.)
