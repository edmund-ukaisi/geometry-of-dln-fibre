# genm-fpcarrier — build spec: the FRONT-PEEL carrier → discharge `(□)` (Stage 2, wiring W1)

**Route decided (controller, 2026-07-10):** FRONT-PEEL `A₀↦A₀·U`, wiring **W1** (prove
`RouteMBoxThresholdFinite M` ∀M by its own arity strong-induction; close `sjJointResolution` as a
corollary). NOT the Γ-atom/decorated/Schur routes. Full grounding: the recon-map
`threads/genm-sjcarrier-recon/recon-map.md` — **READ IT IN FULL FIRST** (it has every banked `file:line`
you consume, the staged pieces, the lessons, and the dead routes to avoid). Also read
`stage2-brief.md` (the charter), `threads/genm-r1substratum/cert.md:150–200` (the `FrontPeelStep`
Lean-ready shape), `threads/genm-vslice/cert.md` (the analytic mechanism + terminal accounting).

## GOAL
`RouteMBoxThresholdFinite M` ∀ nondegenerate `M` (∀ `c' < ½·minAdm M`, `routeMLayerBoxIntegral M c' 1 < ⊤`)
= the `hbox` hypothesis of `aoyagi_learning_coefficient_gen`. Standing invariant: **canonical stays
0-sorry/0-axiom — all gaps live on THIS tide branch only**; every landed piece force-recompiled
`#print axioms` clean-three (S2-free); single-writer on the carrier file.

## THIS TICK'S DELIVERABLE — statements-first skeleton + itemized tide-plan (a CHECKPOINT, not a gate)
1. New carrier file `lean/DLNFibre/DLN/RLCT/Validate/RouteMFrontPeelCarrier.lean` (single-writer, yours).
2. **State** the W1 recursion, statements-first — every not-yet-proven step a cleanly-NAMED `sorry`
   (correct statement; a wrong-statement sorry is worse than none — fix statements first):
   - `frontPeelStep` (r1substratum §C): on `{rank P = q}` write `P = U·V`, `A₀↦A₀·U` (linear surjection
     onto `M₀×q`, kernel dim `M₀·(M₁−q)`) → regime A (`c > M₀q/2`: shift to `∫ tailRankLocus^{−(c−M₀q/2)}`
     via the banked corank bricks `matBox_corank_dominates/residual` + `corankBlock_morsePeel`) / regime B
     (`c < M₀q/2`: `< ⊤` directly). NO Schur, NO `Q_b`, every Jacobian `= 1` (the det-inverse compass).
   - **THE NAMED CRUX** `normalSlice_transfer` (state it, `sorry` it): `{rank P ≤ q}` recurses as the
     shifted `Σ⁰` of `(M₁−q,…,M_L−q)` (normal-slice iso), composing charges ADDITIVELY (the "sum-not-min"
     = paper `addlongest` line 688; vslice-validated at the corner). This is the one real analytic risk; the
     width-general pen-and-paper witness is coming from `vslice` — state the lemma so its proof drops in.
     **SCOPE SPLIT (recon, handoff-saving):** its FINITENESS endpoint is BANKED
     (`radial_morse_residual_power_le` RadialResidualPower:157 at the accumulated block dim +
     `lintegral_eq_polar` RouteMSJSphereBlowup:82) — the OPEN part is ONLY the CoV / singularity-type
     IDENTITY (`{rank P≤q} ≅ shifted Σ⁰`, `addlongest:688`), NOT its integrability. Structure the
     `normalSlice_transfer` statement so the (banked) finiteness leg is CONSUMED and the sorry sits on the
     identity/CoV alone; the vslice witness targets the identity.
   - The arity strong-induction assembling the above into `RouteMBoxThresholdFinite M` — REUSE the shape
     of the banked `routeMBoxThresholdFinite_of_step` (`RouteMSJResolution.lean:863`; arity strictly
     drops, `q≥1` forces reduction → termination, NO extra `(S,J)` kernel needed) + the banked outer
     `routeMLayerBoxIntegral_front_split` (`:461`) + `minAdm_eq_frontPeel` (`RouteMFrontPeelCharge:158`)
     + `frontCharge_ge_minAdm` (`:310`) + `pivotLocus_eq_iUnion` (`RouteMSJPivotChart:307`).
   - Terminal monomial endpoint via the banked `sumSqND_box_lt_top` / `RouteMSJMonomialLower` family.
3. **Close `sjJointResolution` as a corollary** (W1) via `sjJointResolution_of_boxThresholdFinite`
   (`RouteMSJJointReduce.lean:68`) — ⚠ ONLY valid because box-finiteness is proven by the INDEPENDENT
   front-peel recursion, not through the spine (the circularity trap the recon flagged; do NOT call it
   inside the spine). This makes the canonical `sjJointResolution:803` sorry a discharged corollary.
4. **Emit the itemized TIDE-PLAN**: enumerate each named `sorry` in the skeleton with a one-line
   proof-route + a rough size (which banked bricks close it, which need real work). SendMessage the
   team-lead this plan as the checkpoint — it's the effort estimate the operator asked for.

## Consume / avoid (from the recon-map — do not re-derive; do not chase dead routes)
- CONSUME the (a)-list verbatim (front_split, corank bricks, charge combinatorics, pivot-chart cover,
  measurability suite). STAGED (b): `FrontPeelStep` shape + vslice terminal-accounting contract.
- AVOID (d): `RouteMSJChartAlgebra`/`SphereBlowup` (Schur route — NOT this route), the Γ-atom/decorated
  `RouteMSJFreedPeel`/`DecoratedBoxThresholdFinite`, the exponent-preserving #70 fibre-peel, the seam,
  and the off-path sorries (`RouteMSchur:429` etc.). The plain `RouteMBoxThresholdFinite` contract only
  (UPDATE-668; `SJState`/ledger stays INTERNAL, never statement decoration).

## Discipline
- `lean/scripts/lb` ONLY (never bare `lake`); do NOT `lake exe cache get` in the worktree. Green-gate the
  FULL `lake build DLNFibre` before calling any piece integration-ready (catches sibling name-clashes);
  confirm axiom footprints with force-recompiled `#print axioms` (AxCheck), never build exit-0.
- Heed the lessons-map (c): opaque-width → work in the `Params`/Pi form, per-entry diff, no `fin_cases`
  on opaque rows; dependent-dim reassociation via fully-applied `mul_three_reassoc`; `⅟`→`⁻¹` for
  integrand identities; ASCII binders (no `Q̃`/`φ`); `0·∞=0` positivity guard on the corner product;
  `decide +kernel` not `native_decide`.
- Push to a NEW branch `genm-fpcarrier` (`git ls-remote --heads origin genm-fpcarrier` first; if taken,
  `genm-fpcarrier2`). Incremental push; honest partials land continuously. Checkpoint + SendMessage
  (≤180 chars) at: skeleton+tide-plan emitted, then each substantive piece green. Fire a decorrelated
  local-codex-consult if a step's route is ambiguous. Surface ONLY a decorrelated-confirmed non-labour
  wall that no native re-expression routes around (standing decision 7) — else keep building.
