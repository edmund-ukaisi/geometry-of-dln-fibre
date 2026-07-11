# genm-mountain-recon — recon-map: the REMAINING (□)-core mountain (native sjGoodMap route)

**Seat:** self-recon (read-only INTERNAL). **Date:** 2026-07-11. **Base:** canonical HEAD `735f103c`
(`expedition/aoyagi-full`, main checkout, no build). **Charge:** map the banked state for the mountain
build = the OUTER tail integration on the good∪deeper cover + the (S,J) L-recursion (inner slice BANKED).
All `file:line` verified against the live tree at `735f103c`. NO Lean edits, NO builds beyond
`rg`/`scripts/sorries`. All files under `lean/DLNFibre/DLN/RLCT/Validate/` unless noted.

---

## HEADLINE (fold into the build spec)

**The mountain's per-chart CoV is FAR more banked than "inner slice only" — steps (a)+(c) of the
v-exposure are banked, the coercivity-weight bound is banked, the σ_min tail is banked (for the vslice).
The genuine GAP is TWO things, both un-composed: (i) the good∪deeper COVER wiring that splits the
environment `{σ_min(L_θ) ≥ κ}` (inner slice closes) from the deeper front-rank-drop stratum, and (ii) the
front-`Ã₁`-rank-drop DESCENT on the deeper stratum onto a strictly-shorter chain via the IH (the T4 (S,J)
double induction).** The det-inverse is genuinely gone on the native route; the residual mathematical risk
is the SOUNDNESS watch (charges ADD not MIN along the shared rank-drop divisor) re-expressed as: the crude
`σ_min(L_θ)^{−2c'}` coercivity bound may be globally too coarse and want a sharper anisotropic estimate.

**Three CONTRADICTIONS to resolve before speccing** (details in §5):
- **C1 — which gate?** priorities.md item 1 (2026-07-11) says the target is `DecoratedPeelStep`
  (`RouteMSJDecoratedRec:78`) and "803 is OBSOLETE, don't touch." But the LATEST route decision
  (`onepeel-altroute-cert`, same day, 08:49) picks the native `sjGoodMap` route, whose banked chain
  rewrites `gammaPeelIntegral` directly = literally the conclusion of `sjJointResolution` (`:797`, the lone
  live analytic `sorry` at `:803`). **The native route's natural formal target is `sjJointResolution:803`,
  NOT `DecoratedPeelStep`.** Closing 803 discharges `SJStepHyp` via the already-banked `sjResolutionStep_proof`
  and thence `DecoratedPeelStep` via `decoratedBoxThresholdFinite_trivial_iff` — the two gates are equivalent
  (§2), so the choice is a wiring decision, but the native route does NOT "launder" 803, it CLOSES it.
- **C2 — `DecoratedPeelStep` may be UNPROVABLE as stated.** `decoratedpeelstep-instance-cert` (05:29) shows
  the decorated single-peel lands a det-weighted 3-node integral on the PLAIN 3-node box IH, which does not
  cover it. The native route sidesteps this (the IH is used only on the deeper CHAIN, not on a weighted
  integral) — another reason to target 803 via the cover, not `DecoratedPeelStep`'s plain-IH peel.
- **C3 — stale docstring.** `RouteMSJTransport` docstring claims its "output `gammaPeelIntegral_rowSplit_eq`
  writes gammaPeelIntegral as the five-fold integral" — **no such theorem exists** (only
  `gammaPeelIntegral_piSplit_eq`, step (a)). Steps (b)/(c) are un-composed atoms.

---

## 1. The mountain flag + the ACTUAL entry point

- **`chartInner_eq_outerShearFree`** (`RouteMSJGoodChart:389`, **0-sorry**, axiom-clean per `AxCheck:918`)
  — the charge's named flag. States: `∫ A₀∈matBox∩pivotChart, frobSq(A₀·Q)^{−c'} = ∫_{x∈outerDom} ∫_Γ
  freedSchurLoss(x,Γ,Q.submatrix)^{−c'}`. Pure composition of two banked transports (`chartInner_schurWeld_eq_of_emb`
  + `chartInner_schurShearFree_eq`). Its docstring names the un-banked remainder: "identifying `freedSchurLoss`
  with the good-chart `g_cc` via the depth reduction … and the nested finiteness against the endpoint
  `sjGoodMap_loss_matBox_lt_top` on the refined cover." **This is a per-`Q` fixed-tail statement — NOT the
  entry point the build should start from.**
- **★ THE ACTUAL ENTRY POINT: `gammaPeelIntegral_piSplit_eq`** (`RouteMSJTransport:58`, **0-sorry**,
  axiom-clean per `AxCheck:967`). This is one generation past the flag: it composes the whole tail CoV
  (step a) and writes `gammaPeelIntegral M t ρ κ c'` as a nested integral
  `∫_{p.1 = leading layer, M₁×M₂ box} ∫_{p.2 = deeper box} ∫_{x∈outerDom} ∫_Γ
  sjGoodChartLoss(x, Γ, p.1.submatrix(blockSplitEquiv κ), sjDeepFactorCore M p.2)^{−c'}`, with the deep
  factor `sjDeepFactorCore M p.2` proven **independent of the leading layer** (`sjDeepFactor_eFrontTail_symm`).
  The build starts HERE and closes the nested integral.

---

## 2. The (S,J) L-recursion machinery — banked spine vs the open gate

**All the recursion PLUMBING is banked and sorry-free.** The ONLY open analytic content is the per-chart
finiteness `gammaPeelIntegral < ⊤`.

### (a) CONSUME — banked recursion spine (`RouteMSJResolution`, all PROVED)
- **`routeMBoxThresholdFinite_of_step`** (`:863`) — the sorry-free wrapper: strong induction on chain arity;
  `L=0` vacuous (`routeMBoxThresholdFinite_base0`, `:834`), `L=1` Morse base, `L≥2` the step. NO analytic
  content of its own.
- **`sjBase1_freeMatrix`** (`:912`) — the `L=1` free-matrix Morse base, PROVED (via `morseBox_sumSq_lt_top`).
- **`sjBoundaryPeel`** (`:688`) — PROVED sorry-free (CLOSED 2026-07-07): bounds `routeMLayerBoxIntegral M c' 1`
  by `∑_{t,ρ,κ} gammaPeelIntegral M t ρ κ c'`.
- **`sjResolutionStep_proof : SJStepHyp`** (`:849`) — composes `sjBoundaryPeel` (banked) + `sjJointResolution`
  (the sorry). Once `sjJointResolution` closes, this is unconditional and delivers `SJStepHyp`.
- **`SJStepHyp`** (`:824`) — the step contract: `≥3`-width `M` + one-shorter IH ⟹ `RouteMBoxThresholdFinite M`.

### (b) THE OPEN GATE (pick per C1)
- **`sjJointResolution`** (`RouteMSJResolution:797`, **the lone live analytic `sorry` at `:803`**) — given
  the one-shorter IH, `1≤t≤min(M₀,M₁)`, `c'<½·minAdm M`: `gammaPeelIntegral M t ρ κ c' < ⊤`. **The native
  route's conclusion is LITERALLY this** (via `gammaPeelIntegral_piSplit_eq`). Confirmed the sole
  (S,J)-chain sorry by `scripts/sorries` (the other 17 sorries are in the parallel R1-LOWER / Deepest / D1 /
  RouteMSchur machinery, NOT this chain).
- **`DecoratedPeelStep`** (`RouteMSJDecoratedRec:78`) — an unproven `Prop` (a named hypothesis, NOT a sorry).
  Driver `routeMBoxThresholdFinite_of_decoratedPeel` (`:99`, 0-sorry, `AxCheck:973`) gives `→ (□)`;
  `gammaPeelIntegral_lt_top_of_decoratedPeel` (`:111`) gives `→ 803`. **Equivalence:** `DecoratedPeelStep`
  unfolds to `DecoratedBoxThresholdFinite (trivial M)` which `= RouteMBoxThresholdFinite M` via
  `decoratedBoxThresholdFinite_trivial_iff` (`RouteMSJDecorated:217`) — so `DecoratedPeelStep ⟺ SJStepHyp`.
  It is NOT a stronger/more-general object; it is `SJStepHyp` in decorated language.

### The decorated carrier (banked encoding, but see C2)
`RouteMSJDecorated`: `carrierThreshold` (`:64`) `=½·minAdm`; `carrierThreshold_shift` (`:71`, banked, tight
at the binding cut); `SJDecoration` (`:89`); `DecoratedBoxThresholdFinite` (`:148`); `SJDecoration.trivial`
(`:157`) + the π=∅ recovery (`:198`,`:217`, PROVED); `radialAttach` (`:242`) + `radialAttach_decLoss`
(`:262`, PROVED). Decorated peel algebra banked: `freedSchurLoss_absorption`/`_smul`
(`RouteMSJDecoratedPeelCore:41`/`:64`), `lintegral_comp_mulLeftₚ`/`lintegral_box_le_absorption`
(`RouteMSJDecoratedPeelMeas:69`/`:90`, the `|det P|^{−M₂}` gauge CoV, `Matrix.module`-diamond workaround),
`radialAttach_integral_lt_top` (`RouteMSJDecoratedRadialFin`, T3).
**C2 CAVEAT:** `decoratedpeelstep-instance-cert` shows the decorated single-peel→plain-IH reduction is a
mismatch (a 4-node peel lands a det-weighted 3-node integral on the plain 3-node box IH). The decorated
carrier is the anisotropic object that COULD fix this — but only if the recursion's IH is the DECORATED
finiteness, which the current `DecoratedPeelStep` (plain `RouteMBoxThresholdFinite` IH) is not. The native
cover route (§3) avoids this by using the IH only on the deeper CHAIN.

---

## 3. The per-chart CoV — banked steps vs the GAP (the heart of the map)

Starting from `gammaPeelIntegral_piSplit_eq` (§1), the remaining structure and its status:

### (a) CONSUME — the v-exposure CoV atoms (banked)
- **`sjGoodChartLoss_pivotRows_translate_eq`** (`RouteMSJPivotTranslate:41`, 0-sorry, `AxCheck:955`) —
  **step (c), the v-exposure atom**: `∫_U∈matBox sjGoodChartLoss(x,Γ,of(Sum.elim U W),A₂)^{−c'} =
  ∫_{v∈shifted box} sjGoodChartLoss(x,Γ,assembleFront x v W,A₂)^{−c'}`, MP translation `v = U + P⁻¹B₁₂W`.
  Note the RHS box is the SHIFTED `{v | v − P⁻¹B₁₂W ∈ matBox}` — shift unbounded as `P→singular` (the
  environment-degeneration seam, §3-GAP).
- **`rowSplit_lintegral_eq`** (`RouteMSJRowSplit:101`, 0-sorry, `AxCheck:966`) — **step (b)**: leading layer
  `A'0 : M₁×M₂` splits (MP) into κ-pivot rows `Upiv : t×M₂` and corank rows `W : (M₁−t)×M₂`.
- Supporting MP atoms (all banked): `tailParams_pi_split` (`RouteMSJTailSplit`, step a),
  `sjDeepFactor_eFrontTail_symm`/`sjDeepFactor_update_zero` (`RouteMSJDeepFactorCore`/`RouteMSJDeepFactor`,
  A'0-independence of the deep factor), `gammaPeelIntegral_sjGoodMap_eq'` (Classical.choose-free).

### (a) CONSUME — the good-chart inner slice (banked, the 7/2 endpoint)
- **`gammaPeelIntegral_sjGoodMap_eq`** (`RouteMSJGoodCoords:95`, 0-sorry, `AxCheck:928`) — the loss-shape
  bridge to `sjGoodChartLoss`.
- **`sjGoodChartLoss_endpoint_lt_top`** (`RouteMSJVExpose:74`, 0-sorry, `AxCheck:940`) — the joint `(Γ,v)`-box
  finiteness with `v` FREE, for `c' < (a·b + t·h)/2`, given `P` left-inv, `W` right-inv, `A₂` right-inv.
- **`sjGoodMap_loss_matBox_lt_top`** (`RouteMSJGoodChart:269`, 0-sorry, `AxCheck:910`) — the flatten-to-cube
  endpoint via `corner_block_cube_lintegral_lt_top_of_pos`. For (3,3,3,4) t=1: `a=b=2, t=1, h=3` ⟹
  `(4+3)/2 = 7/2 = ½·minAdm(3,3,3,4)`.

### (a) CONSUME — the coercivity-weight machinery (banked; turns per-env slice into a σ_min weight)
- **`corner_block_lintegral_le`** (`RouteMSJCornerBound:55`, 0-sorry, `AxCheck:934`) — **the key mechanism**:
  `∫_{ball R} g^{−c'} ≤ ofReal(a^{−c'})·cornerRadialConst N R c'` for degree-2-homogeneous `g` with uniform
  sphere lower bound `a = min_{‖ω‖=1} g(ω)`. On the good chart `a(θ) = σ_min(L_θ)²`, so the per-env inner
  integral is bounded by `σ_min(L_θ)^{−2c'}·const` — the coercivity weight, det-inverse-FREE.
- **`cornerRadialConst_lt_top`** (`RouteMSJCornerBound`, `AxCheck:933`) — the constant is finite.
- **`exists_uniform_sphere_lb`** (`RouteMSJSphereLB:34`, `AxCheck:945`) — EVT: continuous + pointwise-positive
  on the compact sphere ⟹ the uniform lb `a > 0` exists. `corner_block_lt_top_of_pos` (`AxCheck:946`).

### (a) CONSUME — the σ_min tail integrability (banked for the vslice; banked-adjacent generally)
- **`sjProductTube_params_lintegral_lt_top`** (`RouteMSJProductTube:486`, 0-sorry, `AxCheck:1015`) —
  **LAYER-2, `∫ σ_min(rmatMul (A 0)(A 1))^{−a} < ⊤` over `paramsBoxM (![3,3,4]) 1` for `0≤a<1`.**
  HARD-CODED to the (3,3,3,4) two-layer tail (`![3,3,4]`) and `a<1`; the binding threshold `a<1` ⟺
  `c'<7/2`. Route: box-comparison `sigMin^{−a} ≤ C·det(MMᵀ)^{−a/2}` + exact Gram factorisation
  `det_product_gram` (`:214`, needs the front factor SQUARE) + Tonelli + `detGram_lintegral_lt_top` (`:322`).
  Spectral bedrock reusable at general width: `minStretch`/`minStretch_comp_ge` (`RouteMSJSigMin`, submult),
  `gram_rayleigh_lb` (`RouteMSJRayleigh`), `sigMin_rpow_le_det_rpow_of_mem_box` (`:275`).
- **The good∪deeper COVER skeleton — `setLIntegral_lt_top_of_detMinorCover`** (`RouteMSJDominantCover:173`,
  0-sorry, `AxCheck:1007`) + `setLIntegral_lt_top_of_dominanceCell` (`:151`) + the EXACT partition
  `setLIntegral_eq_sum_dominanceCell` (`:129`, no seam term, arbitrary μ). Reduces box-finiteness to
  per-chart finiteness on a least-index-argmax partition. **This is the cover-assembly for the good∪deeper
  split — it consumes the per-chart bound as a HYPOTHESIS, does not derive it.**

### (b) STAGED for exactly this point (built to be consumed here — highest value)
- `gammaPeelIntegral_piSplit_eq` (`RouteMSJTransport:58`) — staged as the v-exposed entry; DONE step (a).
- `sjGoodChartLoss_pivotRows_translate_eq` + `rowSplit_lintegral_eq` — staged steps (b),(c), UN-composed.
- `corner_block_lintegral_le` + `exists_uniform_sphere_lb` — staged precisely to convert the fixed-env
  inner slice into a `σ_min(L_θ)^{−2c'}` weight for the outer integration.
- `setLIntegral_lt_top_of_detMinorCover` — staged as the good∪deeper cover-assembly (the §SEAM skeleton).
- `sjProductTube_params_lintegral_lt_top` — staged as the LAYER-2 σ_min integrability (vslice-concrete).

### (c) ★ THE GAP — what must be NEWLY PROVEN (priority order)
1. **Compose (b)+(c) into the v-exposed 5-fold form** (the missing `gammaPeelIntegral_rowSplit_eq`, C3):
   apply `rowSplit_lintegral_eq` + `sjGoodChartLoss_pivotRows_translate_eq` to `gammaPeelIntegral_piSplit_eq`,
   a Tonelli reorder bringing `Upiv/v` innermost. **Plumbing, not analytic — but genuinely un-built.**
2. **The good∪deeper COVER wiring** (the environment split). Partition `outerDom × {W,A₂}` by
   `{σ_min(L_θ) ≥ κ}` (good) vs `{σ_min(L_θ) < κ}` (deeper front-rank-drop), via
   `setLIntegral_lt_top_of_detMinorCover` (or dominanceCell). NEW: choosing the key / verifying the split
   is measurable + exact.
3. **The good-branch integration** = combine per-env inner slice (`sjGoodChartLoss_endpoint_lt_top` on the
   SHIFTED box — needs the shift bounded, i.e. `P` bounded away from singular on the good chart) with the
   OUTER `σ_min(L_θ)^{−2c'}` weight via `corner_block_lintegral_le` + the σ_min tail integrability. NEW:
   the shifted-box → unshifted-endpoint uniform bound; wiring the coercivity weight to the ProductTube tail.
4. **★ THE DEEPER-BRANCH DESCENT (the T4 (S,J) double induction, THE HEART).** On `{σ_min(L_θ) < κ}` the
   FRONT factor `Ã₁` loses rank ⟹ a further peel of the front onto a STRICTLY-SHORTER chain, closed by the
   one-shorter IH. NEW: this is the genuine `(S,J)` recursion (front rank descends per level; the deep
   factor `A₂` rank-drop is a Morse codim-rescue, non-binding per `onepeel-tonelli-cert`). This is where the
   still-open analytic content genuinely lives.

---

## 4. The σ_min-integrability route — banked-adjacent vs new (charge item 3)

- The coercivity weight is `a(θ)^{−c'} = σ_min(L_θ)^{−2c'}` where `L_θ` is the 7-dim `g_cc` quadratic
  operator (`onepeel-altroute-cert §2`), NOT the same object as `sigMin(rmatMul (A 0)(A 1))` in
  `sjProductTube`. So the banked ProductTube integrability is the RIGHT SHAPE (a σ_min-power over a factor
  box) but not a drop-in: the build must either (i) relate `σ_min(L_θ)` to a product-of-factors σ_min the
  ProductTube/Gram machinery integrates, or (ii) prove a fresh `σ_min(L_θ)^{−2c'}` integrability.
- **★ THE STANDING CAVEAT (both certs, the residual risk):** the crude `σ_min(L_θ)^{−2c'}` bound "may be
  globally too coarse" (`onepeel-altroute-cert §3`). Its integrability over the tail — OR a sharper
  ANISOTROPIC estimate — is part of the deeper rung. This is the native re-expression of the
  `decoratedpeelstep-instance-cert §4` finding: the det coupling `det(Q_bQ_bᵀ)^{−a/2}` has integrability
  abscissa ≈0.88 < 1 ALONE (not integrable without the reduced core), i.e. the weight's finiteness is
  inseparable from the codim gained on the rank-drop. **Translated to the native route: the good∪deeper
  cover must ADD the deeper stratum's codim to cover the coercivity weight's blow-up — NOT treat them
  independently (which MINs → the RLCT-collapse caricature `z²(x²+y²)`, undershoot to 3/2).**

---

## 5. Pitfalls (c) + DEAD routes (d)

### Pitfalls that bite this build
- **★ SOUNDNESS WATCH — charges ADD not MIN along the shared rank-drop divisor** (`decoratedpeelstep-instance-cert §5`;
  priorities.md Watching). The good∪deeper cover must resolve the deeper (front-rank-drop) stratum by ADDING
  its Jacobian charge (→ 7/2), not letting it degenerate independently (→ min-caricature 3/2). GATE the
  build's close on a decorrelated A₂/front-rank-drop-split check. This is textbook conceptual slop
  (bedrock.md: "technically-correct-but-subtly-wrong"); the base is audited hardest.
- **Binding cut is load-bearing** (`decoratedpeelstep-instance-cert §2/Q3`): the `c'=ab/2` log-borderline is
  interior ONLY on the binding (minimising) cut `u★` — at `M=(4,4,2,2), t=2` it COINCIDES with `½·minAdm`.
  The peel MUST select `exists_binding_cut` (`RouteMSJDecoratedCharge:79`), not an arbitrary legal cut.
- **The shifted-box seam**: `sjGoodChartLoss_pivotRows_translate_eq`'s output box is `{v | v−P⁻¹B₁₂W ∈ matBox}`,
  shift unbounded as `P→singular`. The inner slice `sjGoodChartLoss_endpoint_lt_top` integrates the UNSHIFTED
  `matBox`. Bridging them needs `P` bounded away from singular (the good chart) — do NOT assume the boxes match.
- **`corner_block_lintegral_le` is over `closedBall R`, not a box** — enclose the (shifted) box in a ball first.
- **`det_product_gram` needs the FRONT factor SQUARE** (`RouteMSJProductTube:214`) — the Gram-factorisation
  tail route only Tonelli-splits when the leading factor is square; general-width tails may not split cleanly.
- **`Matrix.module` vs `NormedSpace.toModule` diamond** on matrix-space measure CoV (`lean/CLAUDE.md`): the
  banked workaround transcribes over the raw pi type (`mulLeftₚ`, `lintegral_comp_mulLeftₚ`). Reuse it; do
  not re-hit the diamond.
- **Stale docstrings** (verify against live tree, do NOT trust prose): `RouteMSJTransport` claims
  `gammaPeelIntegral_rowSplit_eq` exists (it does NOT, C3); `RouteMSJResolution:950` calls `sjBoundaryPeel`
  a remaining sorry (it is CLOSED). `#print axioms` / `scripts/sorries` are ground truth.

### DEAD / ruled-out routes (do NOT re-explore or consume)
- **★ The A₂-CASTING route — `RouteMSJOnePeel334` (`onePeel334_cleanCoords_lt_top`, `onePeelIntegral_lt_top`)
  + `RouteMSJCorner334` (`sjCorner334_sector_slice_lt_top`) + `RouteMSJSlice334`.** ABANDONED by
  `onepeel-altroute-cert` (2026-07-11): the `|det M|^{−4}` casting Jacobian is a SELF-INFLICTED A₂-reparam
  artifact (nonintegrable near `{det M=0}`; native `g_cc` stays positive-definite there — Codex
  counterexample `W=[e₁;e₂], v̄=e₁`). **These modules are BANKED + reusable (min→sum / codim-rescue content)
  but OFF the critical path — do NOT consume them into the native build.** (lessons.md 2026-07-11, "2nd
  off-path build".)
- **The det-Jacobian inner atom `corankBlock_morsePeel_lt_top`** (`RouteMSJCorankPeel:114`, banked): the
  `∫_Γ → det(Q_bQ_bᵀ)^{−a/2}·(…)^{−(c'−ab/2)}` route. The native route replaces this det-Jacobian with the
  `σ_min(L_θ)²` coercivity weight — do NOT route the inner integral through `corankBlock_morsePeel` (it
  regrows the det-inverse coupling the instance-cert proved the plain IH cannot absorb).
- **The vsastruct-cert Architecture** (front-majorant/cover; crux `twoBlock_radial_le` `RouteMSJTwoBlockRadial`,
  `RouteMSJFrontSpectral`): a PARALLEL route (banked, reusable spectral bedrock) but OFF this native critical
  path (priorities.md item 1 NOTE). Its MATH (7/2 three ways, coupling load-bearing) informs the cover, but
  do not build on its endpoint.
- **Route-search AROUND the atom** (cornrev equivalence cert): CLOSED by operator decision (A). Do not
  commission tides looking for a strictly-easier sub-problem — build the atom.
- Older DEAD (from prior recon): the ∧²-compound tube (asymmetry); the SEAM det-Jacobian (UPDATE-771); the
  front-peel shortcut (#93).

---

## Reflection (self-recon)

**What to reuse:** start from `gammaPeelIntegral_piSplit_eq` (`RouteMSJTransport:58`), compose the banked
row-split + v-translation atoms, cover with `setLIntegral_lt_top_of_detMinorCover`, close the good branch
with `corner_block_lintegral_le` (→ σ_min weight) + `sjGoodChartLoss_endpoint_lt_top` (7/2), integrate the
weight with the ProductTube/Gram tail. **What to avoid:** the casting route (onePeel334/corner334) and the
det-Jacobian inner atom (corankBlock_morsePeel) — both regrow the det-inverse the native route eliminated.
**What's staged:** the whole per-chart CoV except two un-built rungs. **The genuine GAP is narrow and
located:** (i) the good∪deeper cover wiring + good-branch weight integration, (ii) the front-`Ã₁`-rank-drop
descent onto the shorter chain (the T4 (S,J) double induction) — with the soundness gate that charges ADD
(not MIN) along the shared rank-drop divisor. **Most-likely-to-break:** the crude `σ_min(L_θ)^{−2c'}` bound
being globally too coarse (wants a sharper anisotropic estimate) — the same phenomenon the instance-cert's
abscissa-0.88 finding located, now det-inverse-free. **Before speccing, RESOLVE C1** (target `sjJointResolution:803`
via the cover, not `DecoratedPeelStep`'s plain-IH peel — the two are equivalent, but the native route closes
803 and the decorated plain-IH peel is provably too weak per C2).
