# BUILT-INDEX — the banked (S,J) library for discharging `(□)` = `RouteMBoxThresholdFinite M` ∀M

**Purpose (operator-directed, 2026-07-11).** A durable, consolidated catalog of what is **already banked
sorry-free** toward the (□) discharge, so (a) the §5 lane and future work CONSUME these pieces instead of
re-deriving, (b) nothing built is lost, (c) the map stays honest. Verified against the live tree at
`ef98d885` (`expedition/aoyagi-full`); RE-VERIFY `file:line` at build time (they drift). All modules under
`lean/DLNFibre/DLN/RLCT/Validate/` unless noted. "0-sorry" = `scripts/sorries` clean on the file.

---

## THE ONE OPEN OBLIGATION (the (□)-atom, the whole content of the §5 lane)

**`sjJointResolution` (`RouteMSJResolution.lean:797`, the SINGLE live analytic `sorry` at `:803`).**
Given the one-shorter IH, `1≤t≤min(M₀,M₁)`, `c'<½·minAdm M`: `gammaPeelIntegral M t ρ κ c' < ⊤`. This is
Aoyagi §5's **coupled diag(b) peel** over the corank≥2 / L≥3 strata — radial blow-ups + det-1 unit clears
+ absorption-by-renaming + diag(b) ledger. **Attack it DIRECTLY via §5** (operator, 2026-07-11), with the
library below. Apply the printed **Case-2 typo** note + the **d1kc2 cert #296** (∀-dimension-vector
uniformity, already cleared).

**★ HOUSEKEEPING (2) — ONE object, three names (record this identification):**
`sjJointResolution:803` ≡ `DecoratedPeelStep` (`RouteMSJDecoratedRec.lean:78`, an unproven `Prop`, its
driver proves `→ (□)` AND `→ :803` sorry-free; `DecoratedPeelStep ⟺ SJStepHyp` via
`decoratedBoxThresholdFinite_trivial_iff`) ≡ the `RouteMSJTerminal` scope caveat ≡ the "WALL" certs
(`expeditions/…/r1upper-derisk.md`, `r1upper-wall-review.md`). All name the SAME coupled diag(b) peel.
NOTE (dps-instance-cert): `DecoratedPeelStep` is NOT provable as a plain-IH *single* peel (a det-weighted
3-node lands on the plain 3-node box IH) — it is the decorated DOUBLE induction (the IH carries the
decoration, or the descent lands a strictly-shorter chain). The §5 lane proves 803 = the coupled peel.

---

## THE §5 SCAFFOLD — banked 0-sorry (the §5 lane's LIBRARY)

### Recursion spine (RouteMSJResolution, all PROVED; 803→(□) is banked)
- `routeMBoxThresholdFinite_of_step` (`:863`) — sorry-free driver: strong induction on arity (`L=0` vacuous
  `:834`; `L=1` Morse base; `L≥2` the step). No analytic content.
- `sjBase1_freeMatrix` (`:912`) — the `L=1` free-matrix Morse base (via `morseBox_sumSq_lt_top`).
- **`sjBoundaryPeel` (`:688`) — PROVED sorry-free (CLOSED 2026-07-07)**: bounds `routeMLayerBoxIntegral M c' 1`
  by `∑_{t,ρ,κ} gammaPeelIntegral M t ρ κ c'`. (★ HOUSEKEEPING (1): the docstrings at `:54/:58/:92/:946`
  calling it "(3, … WALL)" / "two remaining sorries" are STALE — only `:803` remains. FIX at the next
  RouteMSJResolution green-gate.)
- `sjResolutionStep_proof : SJStepHyp` (`:849`) — composes `sjBoundaryPeel` + `sjJointResolution`; delivers
  `SJStepHyp` once 803 closes.

### Exponent ledger + terminal (Aoyagi §5's bookkeeping)
- `RouteMSJLedger` (0-sorry): `SJSupport` = the M_{s,k} exponents; `sharedDivisorExp` = the T_{s,k}
  (Case-2 vector); `sjLoss_terminal_lintegral_lt_top` (`:234`) — the (S,J) terminal (dehomogenised
  generator → residual unit ∈ [1,#ι], `∫_{unitBox} (sjLoss e u)^{−c'}·∏|uₗ|^{hₗ} < ⊤`).
- `RouteMSJTerminal` (0-sorry): `terminal_monomial_mul_unit_lintegral_lt_top` (`:160`) — monomial × bounded
  unit `< ⊤` below `monomialThreshold`. (The scope caveat = the open obligation; see identification above.)
- `monomialIntegrand_integrable_of_lt` (`Case222Cover.lean:59`) — the corner-monomial endpoint.
- `RouteMSJMonomialLower` (0-sorry): `iInf_axisRatio_le_monomialThreshold` (`:276`) — S2-FREE lower bound
  `⨅ⱼ (hⱼ+1)/(2kⱼ) ≤ monomialThreshold` (discharges the threshold gate WITHOUT the cited `monomial_rlct`).

### Chart algebra + blow-up CoV (§5's Step-3 + the radial peel)
- `RouteMSJChartAlgebra` (0-sorry): `frobSq_schur_block_split` (`:107`) — the exact block-elimination
  identity `frobSq(A₀·Q)` → `‖A·Q̃ₚ‖² + ‖C·Q̃ₚ+Γ·Q_b‖²` (§5 Step-3).
- `RouteMSJSphereBlowup` (0-sorry) — the polar blow-up CoV.
- `RouteMSJPivotChart` (0-sorry): `measurePreserving_shearSub` (`:337`) — the MP shear `D↦Γ=D−CA⁻¹B`.
- `RouteMSJCorankPeel` (0-sorry): `corankBlock_morsePeel_lt_top` (`:114`) — the corank-block radial Morse
  peel (the det-Jacobian atom `u₀²U₀+u₁²U₁ → det(Q_bQ_bᵀ)^{−a/2}·…`). CAVEAT: emits a det-inverse coupling;
  the NATIVE cover lane replaces it with the σ_min coercivity weight — but for the §5 diag(b) peel it may be
  the native atom (§5 uses diag(b), the det ledger). §5 lane: assess whether to consume it.

### Charge / termination gate (§5's diag(b) ledger + descent)
- `RouteMSJDecoratedCharge` (0-sorry): `peelCharge` (`:45`, `(M₀−u)(M₁−u)`); `minAdm_le_peelCharge_add_redChain`
  (`:52`); `half_minAdm_sub_half_peelCharge_le` (`:67`); **`exists_binding_cut` (`:79`)** — the binding
  (minimising) cut (LOAD-BEARING: the `c'=ab/2` log-borderline is interior only at the binding cut, e.g.
  `M=(4,4,2,2) t=2`).
- `RouteMSJDecorated`: `carrierThreshold` (`:64`, `=½·minAdm`); `carrierThreshold_shift` (`:71`, tight at
  the binding cut); `SJDecoration` (`:89`), `.trivial` (`:157`), `radialAttach` (`:242`,
  MULTIPLICATIVE — the min→3/2 caricature if used cross-level; the additive coupled corner is the fix).
- `RouteMSJDecoratedRec`: the driver `routeMBoxThresholdFinite_of_decoratedPeel` (`:99`, 0-sorry) +
  `gammaPeelIntegral_lt_top_of_decoratedPeel` (`:111`) — both PROVED (gate on `DecoratedPeelStep`).

### The per-chart CoV chain (native-route scaffold, banked 0-sorry)
- Entry: `gammaPeelIntegral_piSplit_eq` (`RouteMSJTransport:58`) — the tail CoV (step a).
- `gammaPeelIntegral_rowSplit_eq` (`RouteMSJRowSplitCompose`, gap 1a BANKED @ef98d885) — + the row-split (b).
- `rowSplit_lintegral_eq` (`RouteMSJRowSplit:101`); `sjGoodChartLoss_pivotRows_translate_eq`
  (`RouteMSJPivotTranslate:41`) — the v-exposure atoms (step c: a measurability rung, IN FLIGHT).
- Inner slice (7/2): `gammaPeelIntegral_sjGoodMap_eq` (`RouteMSJGoodCoords:95`),
  `sjGoodChartLoss_endpoint_lt_top` (`RouteMSJVExpose:74`), `sjGoodMap_loss_matBox_lt_top`
  (`RouteMSJGoodChart:269`) — the (Γ,v)-slice finiteness at `(a·b+t·h)/2 = 7/2`.

### Coercivity / σ_min / spectral bedrock + the sharp anisotropic estimate
- `corner_block_lintegral_le` (`RouteMSJCornerBound:55`) — degree-2-homog → `σ_min^{−2c'}·const` (the CRUDE
  bound; undershoots to c'<½ — see the σ_min-coarseness cert). `exists_uniform_sphere_lb`
  (`RouteMSJSphereLB:34`).
- `sjProductTube_params_lintegral_lt_top` (`RouteMSJProductTube:486`) — LAYER-2 `∫ σ_min^{−a} < ⊤` (`a<1`,
  `![3,3,4]`); spectral bedrock `minStretch`/`minStretch_comp_ge` (`RouteMSJSigMin`), `gram_rayleigh_lb`
  (`RouteMSJRayleigh`), `det_product_gram` (`:214`).
- **`twoBlock_radial_le` (`RouteMSJTwoBlockRadial`, α'=2c'−6)** — the SHARP anisotropic estimate (codims-add);
  `RouteMSJFrontSpectral` (`sigMin²=⨅λ`, `frobSq_ge_twoBlock_of_sector`). ON-path for the native cover lane
  gap (3); relevant to the §5 coupled-corner peel.
- Cover skeleton: `setLIntegral_lt_top_of_detMinorCover` (`RouteMSJDominantCover:173`) — reduces box
  finiteness to per-cell finiteness on an exact least-index-argmax partition (consumes the per-cell bound as
  a HYPOTHESIS). ★ COVER GATE (σ_min-coarseness cert): split on the SECOND-smallest s_{r−1}, NOT σ_min.

---

## REUSABLE BUT OFF BOTH LANES' CRITICAL PATH (banked; keep, don't consume blindly)
- `RouteMSJCorner334` (`sjCorner334_sector_slice_lt_top`, the min→sum validation-in-Lean + the sharp
  divergence boundary), `RouteMSJOnePeel334` (`onePeel334_cleanCoords_lt_top`, the clean-coords codim-rescue),
  `RouteMSJSlice334` — the ABANDONED A₂-casting route (the `|det M|^{−4}` det-inverse was a self-inflicted
  A₂-reparam artifact). Correct + reusable analytic content (min→sum, codim-rescue), but the native route
  uses the sjGoodMap chain instead. Do NOT consume onto the native critical path.

## REFERENCE-ONLY (housekeeping 3)
- The old `aoyagi-rlct` termination kernel (`reference-notes-sj-kernel.md`) — SUPERSEDED by the banked
  driver `routeMBoxThresholdFinite_of_step`. Reference-only (the reference-only protocol, stage2-brief);
  do NOT wire it.

---

## THE TWO LANES (operator, 2026-07-11 — first to (□) wins, both bank; do NOT align/wait on each other)
1. **NATIVE cover / σ_min frontier** (top-down): close 803 via the sjGoodMap inner slice (banked) + the
   outer-tail integration on the good∪deeper cover (split on s_{r−1}) + `twoBlock_radial` → ProductTube +
   the front-rank descent. Gaps: (1a banked) → (1c v-exposure, in flight) → (2 cover) → (3 good-branch) →
   (4 deeper descent). Certs: `threads/genm-mountain-recon/`, `threads/genm-vsastruct/` (onepeel-*, sigmin-*).
2. **DIRECT Aoyagi §5 coupled diag(b) peel** (the paper's method, operator-opened 2026-07-11): prove 803
   directly via §5's recursion (radial blow-ups + det-1 unit clears + absorption-by-renaming + diag(b)
   ledger), consuming the scaffold above. Whole content = the ONE open obligation. Thread: `threads/genm-sj5/`.

## HOUSEKEEPING TODO
- [ ] (1) Fix the stale `RouteMSJResolution.lean` docstrings (`:54/:58/:92/:946`): "two remaining sorries" →
  "one remaining sorry (`sjJointResolution:803`)"; "sjBoundaryPeel (3, … WALL)" → "sjBoundaryPeel (CLOSED,
  sorry-free)". DEFERRED to the next RouteMSJResolution green-gate (avoid contending with the in-flight 1c
  in-place build).
