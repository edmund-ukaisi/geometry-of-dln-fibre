# Next-build render — the math to close `exists_coreResolution:311` (option b, the ideal-route `hideal`)

Phase-checkpoint planning render (2026-07-24), post `survey-inv` kernel-verification. General/thorough; NO
instance-as-justification. Separates **A** (proved, swap/wire) from **B** (genuinely-unbuilt math), with the
**bypass verdict**. Companion to BUILD-STATE.md (the inventory) + ideal-route-full-render.md (the L-A/L-B/Thm-4
spine, rev-render-verified).

## 1. The delivery pipeline — PROVEN (clean-three), a chain of hypotheses
Closing one chart's `hideal` reduces along a proven chain:
- **per-step `StepInv`** (`Core.Aoyagi.StepInvShearChild`, CLEAN): `stepInv_delta0_pullback_child` (δ=0 =
  plain pullback `b'=b∘σ`, trivial/general); `stepInv_delta1_shear_child` (δ=1 = **the coupled Case-1 step,
  "THE WALL's heart"**, proved ABSTRACTLY vs FIX-A/FIX-RESID). Key hypotheses: `σ = blockBlowupMap center
  pivot ∘ sh` (blow-up OUTERMOST — the monument/L7 order, so **SEAM-1 composition-order is RESOLVED in the
  step algebra**), `sh` pivot-keeping, and **`hsupp`: the parent residual is a center-coordinate combination
  `residⱼ u = ∑_{i∈center} cⱼᵢ u · uᵢ`**. Produces the child residual as the STRICT TRANSFORM
  (`blockBlowupCoordQuot`), witness `q'=q∘σ`.
- **`terminal_bezout`** (CLEAN): at the terminal (residual trivial) + a cleared pivot `(Fᵢ₀∘g)=b·unit`,
  `unit 0≠0`, invert on `{unit≠0}` ⟹ upgrade `StepInv` (divisibility) to `PrincipalInv` (the ideal identity
  `⟨F∘g⟩=⟨b⟩`, both ways).
- **`principalInv_regionRepresents`** (L1, CLEAN): `PrincipalInv → hideal_fwd ∧ hideal_bwd` (the
  `RegionRepresents` both ways = the `Chart.hideal` fields).
- **`chart_of_collapse` / L6′ / L8′** (CLEAN): `hideal` + `hcollapse` (`|jacDet gmap|=jacWeight jac`, unit≡1)
  ⟹ a fully-certified `Chart (coreGen d e) 0`.
So GIVEN the fold emits (per chart) terminal `PrincipalInv` + `FoldRealizes` (the collapse `hcollapse`), the
`Chart` → `AtlasRealizesExponents` → `:311` follow (modulo the import-cycle + `hcover`). The value half
(`hlb`+`hattain`) + D12 are already clean-three.

## 2. THE BYPASS VERDICT (the crux the survey surfaced)
The ideal-route fold, built via the CLEAN per-step children (`stepInv_delta0/delta1`), **SUPERSEDES** the
geometric-fold's per-step `case1/2_preserves_stepInv''` (which carry `sorryAx` via the frontiers): the
abstract δ=1 shear child IS the coupled Case-1 step, proven. **BUT it does NOT bypass the WALL** — the child
emits the residual as the strict transform, and to feed the NEXT δ=1 step the fold must maintain `hsupp` (the
child residual is again a center-combination). That maintenance IS `realBranch_appendResidDescent`. Verdict:
- **per-step maintenance: bypassed-to-clean** (`stepInv_delta1_shear_child`, done).
- **the invariant-carry (`hsupp` down the branch = `appendResidDescent`): NOT bypassed** — but it is exactly
  the render's **L-B (the b-chain divisibility absorbing the block-elim cross-terms), rev-render #3-verified
  sound**. So it is render-bounded, Lean-unbuilt — NOT open math.

## 3. B — the genuinely-unbuilt residual (general)
- **B1 `leaf_stepInv_of_path` (the fold-INDUCTION).** Compose `stepInv_delta0/delta1` (clean) + the `hsupp`
  carry (B2) down `buildTree`; subsume→`LastLayerInv` at `S=L` (B4); hand the terminal edge to
  `terminal_bezout` (clean); EMIT a `GeoAtlasData` + `FoldProduced` + `FoldRealizes` + per-chart terminal
  `PrincipalInv`. A genuine CONSTRUCTION (the structural induction + the emit-bookkeeping) — tractable given
  the atoms, but real; the missing statement = the theorem body.
- **B2 `realBranch_appendResidDescent` (the WALL = the `hsupp` invariant-maintenance).** The strict-transform
  child residual stays a center-combination through the coupled-corank≥2 recursion. RENDER-VERIFIED (L-B,
  b-chain, rev-render #3). Lean-unbuilt. The genuinely-hard coupled piece, but render-bounded.
- **B3 `foldResid_case11_mergeBoostSplit_canon` (Case-1(1) merge boost-split).** OPEN QUESTION (to settle in
  the deeper render + rev-render): is it SUPERSEDED by `stepInv_delta1_shear_child` (does the abstract δ=1
  child already cover the Case-1(1) merge), or does the fold still route through it? If superseded, it drops
  from B.
- **B4 `lastLayer_clear_preserves` (S=L clear).** The terminal-layer handling (`LastLayerInv` + conditional
  `GeneratorCleared`) feeding the terminal handoff. Bounded.
- **B5 `leafPath_compactCover` (the coupled `hcover`).** `ball 0 ρ ⊆ ⋃ (gmap''dom)`. UN-PROBED at corank≥2 —
  the highest residual risk (charter §3 + elder gate). The box-geometry (`GeneralGeoAtlas`) mechanisms are
  for a SIMPLER single-term-shear object; the faithful coupled cover is unbuilt. **PROBE decorrelated
  BEFORE committing the full fold** (elder gate ii). Independent of the fold-induction.

## 4. A — proved, swap/wire (scout-verified; NOT the math, the plumbing)
- Swap unprimed L6/L8 `sorry` → `leafPath_chartGeometry'`/`leafPath_realizesExponents'` (clean). Terminal
  handoff (`terminal_bezout` + `terminal_edge_stepInv`), `case2_conjA`, homogeneity twins — clean (some
  consumer-less today). **Blocker:** the import cycle — `exists_coreResolution` lives upstream in
  `LearningCoefficient`, so the in-place `:311` sorry can't consume the primed driver without a
  `coreGen`/`flatDim` reorg OR promoting the primed driver canonical. A wiring task, not math.

## 5. Open questions → the deeper render + rev-render review
- (Q1/B3) Is `foldResid_case11` superseded by `stepInv_delta1_shear_child`, or a distinct merge obligation?
- (Q2/B2) Is `appendResidDescent` EXACTLY the render's L-B (so render-bounded), or does its Lean statement
  carry more than L-B verified (e.g. the `supportAt`/center bookkeeping)?
- (Q3/B5) The corank≥2 `hcover` probe — the un-probed highest risk; decorrelated exact geometry.

**NET (honest, corrected):** the residual is NOT "swap+wire", and NOT "the whole monument unbuilt". It is:
the fold-INDUCTION (B1, a construction over proven atoms) + the `hsupp` invariant-carry (B2 = render-verified
L-B, Lean-unbuilt) + the coupled `hcover` (B5, un-probed = the real risk) + [B3 possibly superseded, B4
bounded] + the A-plumbing/import-cycle. The per-step algebra + the whole delivery pipeline are proven; the
coupled hardness lives in B2 (render-bounded) and B5 (un-probed). The elder gate stands: prototype (B2 at
corank-2, dom-wide two-sided `hideal`) + probe (B5 corank≥2), green-both before the full fold.
