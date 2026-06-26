# Thread 36 — general achiever Jacobian determinant: route adjudication

**Seat:** scout (recon/design). **Date:** 2026-06-26. **Branch:** `expedition/aoyagi-full`.
**Mandate:** adjudicate the route (a / c / hybrid) for the ∀M achiever-chart Jacobian determinant
`|det Dφ_{M,t}| = ∏_j |u_j|^{leafH j}` — the ONE residual gating
`routeMCore_box_diverges_achiever` ∀M (`RouteMLayerCoverGE.lean:130`) — and hand the controller a
broken-down, bounded build plan.

## Deliverable

`design.md` (this thread): route recommendation + the parametric Schur-frame det theorem + the
Mathlib route + the flat-coordinatization plan + the Phase A/B/C bounded build plan + the
(3,3,3,3) cross-check.

## Headline (the reversal vs the wall report `be84b67b`)

The prior wall report scoped the general det as "multi-week parametric Schur-frame/LDU determinant"
and recommended shipping only the 3 anchors. **That estimate predated the structural collapse found
here:** the per-boundary Schur differential is BLOCK-LOWER-TRIANGULAR (TL,TR,BL,BR ↔ dK,dN,dX,dE),
with diagonal blocks `1, K·(−), (−)·K, 1` — so `|det| = |det K|^{r+c}` via `det_pi`, with NO
per-instance SCC `frameB` grading. The det is now a BOUNDED local theorem; the keystone has MOVED to
the flat-coordinate decoder identity `chartParamsFlat = chartParamsGen`.

## Verification (decorrelated, three angles)

- `my_schur_det.py` — independent symbolic check `|det DS| = (det K)^{r+c}` over 10 (t,r,c) profiles. ✓
- `schur_factorization.py` — the differential is block-lower-triangular AND det-correct, all profiles. ✓
- `full_det_check.py` — full-chart (2,2,2) det: u-exp = `minAdm−1`, spectator unit ratio. ✓ (3,3,3,3
  cert-verified upstream, `verify_codex_3333.py`).
- `codex/route-{prompt,answer}.md` — decorrelated xhigh Codex consult. Confirms route (c) + rate
  transfer via `phiGen`; keystone = `chartParamsFlat_eq_chartParamsGen`; det now bounded; injOn
  structural; prefix-fold genuinely needed.
- Standalone Lean elaboration (`/tmp/det_mulleft_check2.lean`, `/tmp/det_conj_check.lean`,
  Mathlib-only) — A1 det-pi route pieces all elaborate clean against the v4.29 pin. The det engine is
  de-risked.

## Recommendation

Route **(c)** for det/cov; rate-transfer via the banked `routeMCore_phiGen`. Keystone =
`chartParamsFlat_eq_chartParamsGen` (C1); riskiest = C1 then the B2 prefix-fold. The det (A1–A3, B3)
is bounded/routine. ≈ 8–10 scoped lemmas across 3 phases — a chargeable sequence of bounded sub-builds,
NOT an open design problem. Full plan in `design.md §4`.

## No Lean edits (recon only). Artefacts: design.md + 3 verify scripts + the codex pair.

---

## UPDATE (formalisation tide, 2026-06-26) — item 2 DONE ∀M; item 3 = an ARCHITECTURAL wall (decoder redefinition), not a tactical induction

Banked sorry-free + axiom-clean `[propext, Classical.choice, Quot.sound]` (force-elaborated
`#print axioms`), on branch `worktree-agent-a3901f84e4049cbfa` (off `expedition/aoyagi-full`):

- **`RouteMConjBlock`** — the generic det-preserving block-conjugation workhorse. `conjBlockMap`/
  `conjBlockDeriv`/`conjBlock_hasFDerivAt`/`conjBlock_abs_det`: conjugate any nonlinear factor
  `g : B → B` (fderiv `gD`), identity on a rest `R`, into a full-ambient `ChartFactor N` via ANY
  `E : (Fin N → ℝ) ≃L B × R`; `|det D| = |det gD|` at the prefix block `(E u).1` (the rest washes
  out via `det_prodMap`+`det_id`, `det_conj` preserves). This REPLACES the heavy `ChartIdx`
  coordinatization for the DET (Codex-confirmed) — the det needs only SOME CLE.
- **`RouteMFactorFDeriv`** — the matrix-valued fderiv plumbing: diamond-free pi-norm
  `NormedAddCommGroup`/`NormedSpace`/`FiniteDimensional` on `Matrix (Fin l)(Fin m) ℝ` (norm topology
  `= rfl` the canonical matrix product topology), the matrix-mult continuous bilinear CLM `matMulBilin`
  (layered `mulLeftCLM` + outer), and the product rule `HasFDerivAt.matMul`.
- **`RouteMFactorMaps`** — item 2 COMPLETE. `schurFrameMap`/`lduCoreMap` (the nonlinear factor maps)
  with `HasFDerivAt` matching the banked Phase-A differentials (`schurFrameDeriv`/`lduCoreDeriv`) —
  Schur by the product rule over the 4 output blocks + entrywise match (`schurFrameDeriv_apply`,
  `noncomm_ring`/`add_mul`+`abel`); LDU by the triple-product rule + linear `matrixSplit` compose
  (matched to `lduDerivMat_apply`); chain via the banked LINEAR `chainUnitMap` (det 1).
  `schurChartFactor`/`lduChartFactor`/`chainChartFactor` (+ `_abs_det`): the three conjugated
  `ChartFactor N`s, parametric in the ambient-split CLE `E`, with their monomial dets.
- **`RouteMPhiFlatDet`** — the item-4 det ASSEMBLY skeleton. `phiFlat_abs_det_of_factored`:
  `|det (fderiv φ_flat u)| = ∏_j |u_j|^{leafH j}` GIVEN (item 3) `composeFold fs = phiFlat` +
  (item 4 bookkeeping) the per-factor det product = the leafH monomial. The det telescope between
  them is closed (`composeFold_abs_det` banked); `phiFlat_hasFDerivAt_of_factored` pins the factored
  fderiv from the map equality. So the DET SIDE is complete modulo item 3 + the leafH summation.

### The precise item-3 wall (re-scoped — INDEPENDENTLY confirmed by xhigh Codex, `codex/item3-wall-*`)

The keystone was thought to be `chartParamsFlat = chartParamsGen` (`rfl`, banked). The GENUINE
keystone is the FLAT map equality `composeFold fs = phiFlat`. It is UNPROVABLE with the current
`genBlkFlat` (`RouteMGenFlatChart.lean:65`): its decoder is an arbitrary MODULAR HASH
(`x ((i*31+j*7+…) % N)`) chosen because the RATE is coordinate-agnostic. Codex's concrete obstruction:
`L=1, M=(1,7)` ⟹ `Rfin 1` reads `x((j*7+17)%7) = x 3` for EVERY `j` — 7 block entries collapse to one
flat coordinate. No honest block-extraction CLE (independent block functionals) can match a hash that
identifies distinct entries; the `%N` overlap breaks injectivity-on-blocks, so it cannot be absorbed
into the `E_s` either.

**The fix (multi-pass, NOT a research wall):** REDEFINE `genBlkFlat` to decode block data via the
`chartIdxEquiv` role-slot coordinatization (disjoint structured slots, one summand per role), and build
the factor CLEs `E_s` from the SAME coordinatization (shared accessors). Then `composeFold fs = phiFlat`
is accessor lemmas + boundary induction, not a late extensional fight.

**Index alignment (confirmed, derived + Codex):** the Schur frame at boundary `s` has size
`(t_s+r_s)(t_s+c_s) = t_{s-1}·M_s = schurDim (s-1)`, NOT `schurDim s`. (3,3,3,3) check: frame `s=1`
size 9 = `schurDim 0`; frame `s=2` size 6 = `schurDim 1`. ✓

**Rate transfer SURVIVES the redefinition:** `routeMCore_phiGen` consumes only `GenBlk`/`hle`/`hC0`,
not the decoder — re-check `hC0` (identity boundary `Bmat 0 = I`, `Rmat 0 = 0`, `t_0 = M_0`) under the
structured decoder; audit downstream a.e.-positivity/unit facts separately if they read the decoder.

**Next-tide plan:** (1) structured `genBlkFlatStruct` via `chartIdxEquiv` role slots + the
`(Fin schurDim → ℝ) ≃L SchurInc`/`LDUParam`/chain flattening CLEs (`finrank SchurInc = (t+r)(t+c)`
verified, so `ofFinrankEq` exists — but must be the STRUCTURED one, sharing accessors with the
decoder, not abstract); (2) the factor list `fs` from those CLEs; (3) `composeFold fs = phiFlat` by
boundary induction; (4) re-check `hC0`; (5) the leafH summation (item 4) via `leafH3333_prod_eq`
pattern; (6) `phiFlat_abs_det` via the banked `phiFlat_abs_det_of_factored`.
