# Recon-map — the `(3,3,3,4)` contracting-tail vertical slice (self-recon `genm-vsrecon`)

**Seat:** self-recon (INTERNAL). **READ-ONLY** (no Lean edits; `rg`/`git`/file reads only).
**Verified against the LIVE tree:** branch `expedition/aoyagi-full` @ `cdeca1e2` (UPDATE-859), NOT the log.
All `file:line` re-checked against the current source. **NO new claims.**

## Headline (fold into the vslice spec)

**The vslice's feared "new brick" is already banked.** The corner blow-up + unit-boundedness — the
vslice cert §5/§8's "single load-bearing surprise" and "most likely thing to break it" — is landed
**sorry-free, WIDTH-GENERAL** as `RouteMSJSlice334.sjSlice_corner_two_block_lt_top` (`:77`), via a
**weighted-AM-GM** route that *sidesteps the general-width CoV Jacobian entirely* (units threaded as the
hypothesis `a ≤ Uᵢ`, exactly like the terminal endpoint's `hunit`). The `(3,3,3,4)` instance at the
binding threshold `c' < 7/2 = ½·minAdm` is `sjSlice334_corner_lintegral_lt_top_of_lt_half_minAdm`
(`:251`); `sjSlice334_minAdm_eq` (`:243`) proves `minAdm(3,3,3,4)=7`. UPDATE-806 already integrated this
"FIRST (S,J) build slice" reviewer-cleared; UPDATE-859 gates the whole slice GREEN on the analytic side.

So the vslice is **overwhelmingly a COMPOSITION/wiring task over banked, sorry-free, aggregator-imported
modules** — front-split → pivot-cover → Schur split → depth-reduce → corank radial → **this banked
corner crux** → monomial endpoint → `minAdm` accounting. **Every stage has a banked lemma with a verified
`file:line`.** The one real open is the single sorry `sjJointResolution` (`RouteMSJResolution:803`) — and
for the DEEPER strata `{rank Q_b ≤ b−2}` inside it, the B5-desc corank-Gram **chain-length descent**,
whose *math is PROVEN* (subred) but whose **Lean dominant-minor cover-assembly is the one un-built,
stall-prone piece** (the det-inverse §8-i obligation).

**What to reuse:** the full stage table in (a) — call the exact names, don't re-derive. **What's staged:**
the whole `RouteMSJSlice334` module + the `gammaPeelIntegral_sjGoodMap_eq`/`_eq'` bridges +
`frontPeel_binding_cut` (built by descN *for this slice*, with a `decide` anchor `minAdm(3,3,3,4) =
frontCharge 2`). **What to avoid:** dyadic `|det α|`-shells, `D_free`, the `[free-Q core]∘[loss IH]`
factorization, the literal native inner (S,J) loop, and a bare `|det B|`-peel (not dominance-restricted).
**What must be built fresh:** the composition into `sjJointResolution` + the B5-desc **Lean cover-assembly**
+ the B5b disjoint-block RLCT-add wiring — see the FRESH-BUILD list.

---

## (a) CONSUME — banked, sorry-free on canonical, aggregator-imported. Reuse by name.

Stage order = the charge's pipeline. All `file:line` verified `expedition/aoyagi-full @ cdeca1e2`.
Path prefix `DLNFibre/DLN/RLCT/`. All real-sorry counts checked = 0 unless noted.

### Cover → front-split → pivot-chart (banked, CLOSED)
- `routeMLayerBoxIntegral_front_split` — `Validate/RouteMSJResolution.lean:461` (peel leftmost layer, MP)
- `gammaPeelIntegral` (def, the raw chart integral the sorry bounds) — `RouteMSJResolution.lean:517`
- `pivotChartCover_lintegral_le_sum` — `RouteMSJResolution.lean:531` (cover subadditivity, CLOSED)
- `pivotChartCover_matBox_le_sum` — `RouteMSJResolution.lean:552`
- `sjBoundaryPeel` — `RouteMSJResolution.lean:688` (**sorry-free now** — the block-reindex plumbing closed)
- `pivotLocus_eq_iUnion` — `Validate/RouteMSJPivotChart.lean:307`
- `isUnit_submatrix_le_rank` — `RouteMSJPivotChart.lean:289`

### Schur block split + MP shears (COMPASS #1 — `a⁻¹` lives only in det-1 shears)
- `frobSq_schur_block_split` — `Validate/RouteMSJChartAlgebra.lean:107` (BANKED EXACT)
- `measurePreserving_shearSub` — `RouteMSJPivotChart.lean:337` (BANKED MP `D↦Γ`)

### Depth reduction (§4a) → good-chart loss bridge (the sorry's LHS rewrite)
- `gammaPeelIntegral_sjGoodMap_eq` — `Validate/RouteMSJGoodCoords.lean:95` (**bridge: `gammaPeelIntegral = ∫∫∫ sjGoodChartLoss^{−c'}`; axiom-checked in AxCheck.lean:918**)
- `gammaPeelIntegral_sjGoodMap_eq'` — `Validate/RouteMSJDeepFactor.lean:81` (measure-side, explicit deep factor, `Classical.choose`-free; AxCheck:943)
- `sjGoodMap` / `sjGoodMap_injective` / `sjGoodMap_loss_pos` — `Validate/RouteMSJGoodLoss.lean:54/76/128`
- `sjDeepFactor` / `sjTail_factor_explicit` / `sjDeepFactor_update_zero` — `Validate/RouteMSJDeepFactor.lean:37/51/66`
- `freedSchurLoss_eq_sjGoodMap` / `_mul` — `Validate/RouteMSJDepthReduce.lean:46/67`
- `twoMatBox_injectiveLinear_lintegral_lt_top` — `Validate/RouteMSJGoodChart.lean:44` (good-stratum finiteness leaf)

### Corank-2 → 1 radial (§4b)
- `corankStep` / `corankStep_prefactor` / `corankStep_sequential` — `Validate/RouteMSJCorankStep.lean:88/105/118`
- `corankBlock_morsePeel_lt_top` — `Validate/RouteMSJCorankPeel.lean:114`
- `matBox_corank_residual_le` — `Validate/RouteMSJCorankResidual.lean:114`
- `matBox_corank_residual_absZ_le` / `matBox_corank_dominates_absZ_lt_top` — `Validate/RouteMSJCorankPure.lean:130/87`
- `SJDecoration.radialAttach` — `Validate/RouteMSJDecorated.lean:242`; `radialAttach_integral_lt_top` — `Validate/RouteMSJDecoratedRadialFin.lean:45`; `radialAttachFactor_lt_top` — `Validate/RouteMSJDecoratedRadial.lean:65`
- `radial_morse_residual_power_le` — `Validate/RadialResidualPower.lean:157` (⚠ hyp reads `(m+1)/2 < c'` but the STATEMENT is an UPPER bound `∫ ≤ Cresid·w^{−(c'−(m+1)/2)}` — a genuine *finiteness/residual-power* bound, name matches content; verified in-file)

### ★ CORNER crux (§5) + unit-boundedness (§8) — the former "new brick", now BANKED width-general
- **★ `sjSlice_corner_two_block_lt_top`** — `Validate/RouteMSJSlice334.lean:77` (general `h0,h1`; units as `a ≤ Uᵢ` on `unitBox 2`; **AM-GM weights `((h0+1)/s,(h1+1)/s)`, sidesteps the CoV Jacobian**; SORRY-FREE)
- `sjSlice334_corner_lintegral_lt_top` — `RouteMSJSlice334.lean:205`
- `sjSlice334_corner_lintegral_lt_top_of_lt_half_minAdm` — `RouteMSJSlice334.lean:251` (the `(3,3,3,4)` payoff, `c'<7/2`)
- `sjSlice334_minAdm_eq` — `RouteMSJSlice334.lean:243`; `sjSlice334_symmetric_undershoot` — `:233` (the misleading `3/2` min documented)
- `prod_rpow_lintegral_Ioo_box_lt_top` — `Validate/RouteMSJMonomialLower.lean:87` (the separated-monomial endpoint AM-GM lands on)
- `corner_block_cube_lintegral_lt_top_of_injective` — `Validate/RouteMSJCornerGate.lean:80`; `corner_block_lt_top_of_bound` — `Validate/RouteMSJCornerBound.lean:117`
- `exists_pos_lower_bound_on_sphere` — `Validate/RouteMSJCornerGate.lean:38` (**the a.e.-pos → uniform unit bridge — the §8 "bounded-below cores" brick B5d**)
- `frobSq_rmatMul_smul` / `measurable_frobSq_rmatMul` — `Validate/RouteMSJCornerLoss.lean:36/47`

### Monomial endpoint (§6 / B7) + L=1 base
- `monomialIntegrand_integrable_of_lt` — `Validate/Case222Cover.lean:59`
- `terminal_monomial_mul_unit_lintegral_lt_top` — `Validate/RouteMSJTerminal.lean:160`
- `sjBase1_freeMatrix` — `RouteMSJResolution.lean:912`

### Accounting = ½·minAdm (§6 / B5b / descN #117)
- `Mval` — `Foundations/Lambda.lean:41`; `Adm` — `Lambda.lean:62`
- `minAdm` — `Validate/RouteMLayerSplit.lean:51`; `minAdmRec` — `:58`; `redChain` — `:40`
- `Mval_decompose` — `RouteMLayerSplit.lean:96`; `minAdmRec_eq_minAdm` — `:395`
- `minAdm_eq_frontPeel` — `Validate/RouteMFrontPeelCharge.lean:158`; `frontCharge` — `:111`; `tailMin` — `:106`; `frontCharge_ge_minAdm` — `:310`
- **★ `frontPeel_binding_cut`** — `Validate/RouteMSJDescNat.lean:57` (descN #117; `∃ q ≤ tailMin M, minAdm M = frontCharge M q`; has `decide` anchor `minAdm(3,3,3,4)=frontCharge 2` in-file)
- `exists_binding_cut` — `Validate/RouteMSJDecoratedCharge.lean:79` (layer-peel saturation)
- `sjChargeBudget_le` — `RouteMSJResolution.lean:203`; `sjChargeUpdate_accum` — `:353`

### Driver + recursion glue (Tier 0/4)
- `routeMBoxThresholdFinite_of_decoratedPeel` — `Validate/RouteMSJDecoratedRec.lean:99` (D0 driver, BANKED)
- `DecoratedPeelStep` (Prop) — `RouteMSJDecoratedRec.lean:78`; `gammaPeelIntegral_lt_top_of_decoratedPeel` — `:111`
- `routeMBoxThresholdFinite_of_step` — `RouteMSJResolution.lean:863` (**the ACTUAL termination carrier — arity strong induction**; see §CONTRADICTIONS re the phantom kernel)
- `SJStepHyp`/`SJBaseHyp` — `RouteMSJResolution.lean:824/829`; `sjResolutionStep_proof` — `:849`
- `sjJointResolution_of_boxThresholdFinite` — `Validate/RouteMSJJointReduce.lean:68` (retro-fills `:803` from box-finiteness — the W1 corollary route)
- `carrierThreshold` / `carrierThreshold_shift` — `Validate/RouteMSJDecorated.lean:64/71`
- `decoratedBoxThresholdFinite_trivial_iff` — `RouteMSJDecorated.lean:217`
- `RouteMBoxThresholdFinite` (def) — `Validate/RouteMBoxReduction.lean:165`

### Leaf bricks (both integrated to canonical, per charge — confirmed)
- **B4** (`b=1` free-bilinear): `freeBilinear_box_lt_top` — `Validate/RouteMSJFreeBilinear.lean:117`; `frobSq_rmatMul_corank_one` — `:67`
- **Cat I** (free-Q leaf): `qbox_lintegral_lt_top` — `Validate/RouteMSJQBoxCore.lean:113`; `det_gram_cons` — `Validate/RouteMSJGramResidual.lean:194`
- Radial Morse: `sumSqND_box_lt_top` — `Foundations/S1RadialMorse.lean:67`; `morseBox` — `:32`; `radial_morse_dominates_lt_top` — `:127`
- `integrableOn_norm_rpow_neg_ball` — `Validate/RouteMSJRadialInt.lean:29`

---

## (b) STAGED — designed for exactly this point (highest-value; exist to prevent re-derivation)

1. **The whole `RouteMSJSlice334` module** (thread `genm-sjslice`) is STAGED FOR THE VSLICE — the corner
   crux width-general + the `(3,3,3,4)` instance theorems. It is the "FIRST (S,J) build slice" (UPDATE-806).
2. **`gammaPeelIntegral_sjGoodMap_eq` / `_eq'`** — the bridges rewriting the sorry's LHS
   (`gammaPeelIntegral M t ρ κ c'`) into the good-chart / explicit-deep-factor loss form the corner crux
   consumes. Axiom-checked in `AxCheck.lean`. These EXIST to be composed here.
3. **`frontPeel_binding_cut`** (`RouteMSJDescNat:57`) — built by descN (#117) FOR the vslice accounting,
   with in-file fidelity anchors (`decide`: `minAdm(3,3,3,4) = frontCharge 2`; the sub-generic `(4,4,2)`
   twist anchor). It is the min-tail binding cut B5b selects (front-peel analogue of `exists_binding_cut`).
4. **`carrierThreshold_shift` + `decoratedBoxThresholdFinite_trivial_iff`** — the decorated-carrier peel
   drop-in (peel at `u★`, land on `redChain u★ M` at `carrierThreshold − ½·peelCharge`, closed by hIH).
5. **`sjJointResolution_of_boxThresholdFinite`** — the retro-fill so the W1 front-peel route (prove
   `RouteMBoxThresholdFinite` ∀M by arity induction) closes the `:803` sorry as a COROLLARY, avoiding the
   Schur/SphereBlowup machinery for the sorry itself.
6. **The `(S,J)` carrier ops** — `SJDecoration.trivial` (`RouteMSJDecorated:157`), `radialAttach` (`:242`),
   `rowMix` (`RouteMSJDecoratedRowMix:56`), `loss_blockSplit` (`RouteMSJLinGen:290`) — staged for the
   decorated route.

---

## (c) LESSONS / caveats that BITE this build (pull into the spec)

1. **★ ANTI-TRAP (descN, UPDATE-859): `tailMin − b + 1 ≠ minAdm`.** The corank-Gram fixed-stratum
   integrability threshold `min(tail)−b+1` is NOT `minAdm` (two-width `(2,2)`: threshold 1 vs `minAdm`=4).
   The composition to `minAdm` is the **FRONT-PEEL** (`minAdm_eq_frontPeel` at `j=q−1` = `frontPeel_binding_cut`).
   Do NOT report `tailMin−b+1` as an RLCT threshold — it is a Level-A per-stratum threshold, not the value.
2. **pivchg DOMINANCE-RESTRICTION (§SEAM, UPDATE-858):** dominance-restrict each chart `{|det B| ≥ others}`
   OR bound `g` geometrically via `σ_q` — NEVER a bare `|det B|`-peel (over-charges the codim-1
   `{det B=0, rank=q}` locus; witness `P(t)=[[1,0,0],[0,t,t²]]`). Do NOT introduce an inverse-minor-gap
   factor `(|det Bᵢ|−|det Bⱼ|)^{−1}` — there is none in `g`.
3. **CONTRACTING-TAIL requirement (M₂ < M_last):** `(3,3,3,4)` tail `(3,3,4)` has `M₂=3 < M_last=4` — GOOD,
   it exercises the twist. Use `D_prod = minAdmRec(reduced by q−1) = (8,4,1)`, STRICTLY below
   `D_free=(12,6,2)` (which over-admits `c'` past `½·minAdm`). A balanced chart hides the twist and
   silently validates the WRONG threshold.
4. **min-vs-sum (vslice §5 / Slice334 docstring):** the binding local model is a **SUM** `u₀²U₀ + u₁²U₁`,
   NOT a product `(u₀u₁)²`. `{u₀=0}`/`{u₁=0}` in isolation give the misleading undershoot `min(2,3/2)=3/2`;
   the corner binds (codims ADD, `4+3=7`). The AM-GM route sidesteps the explicit CoV Jacobian.
5. **B4 ±1 charge-composition:** `½·min(a+1, D+1) → ½·minAdm` at the `b=1` binding cut (flag for B6).
6. **Level-A vs Level-B (x⁴+y⁶ discipline):** the vslice proves **Level-A integrability** (`<⊤` = `(□)` =
   `rlct ≥ ½·minAdm`), NOT the Level-B value `= ½·codim` (which rides on the cited Watanabe-universal upper
   bound). Never name a finiteness brick as if it proved the RLCT value. The tie→log at `q=2` is a Level-B
   θ-count signature, harmless to the strict Level-A threshold.
7. **Matrix.module diamond (lean/CLAUDE.md):** matrix-space measure CoV hits the `Matrix.module` vs
   `NormedSpace.toModule` instance diamond. Transcribe the map over the RAW pi type (`Fin c → Fin t → ℝ`),
   column-indexed — det factors via `det_pi` to `(det K)^c`. Pattern: `RouteMSJDecoratedPeelMeas.mulLeftₚ`.
   Recurs in composed chain-products.
8. **Opaque-width / dependent-dimension casts (lean/CLAUDE.md):** matrix-apply `simp` "no progress"
   in-context at dependent widths — use `have`+`exact` at explicit `⟨_, by decide⟩` indices;
   `mul_three_reassoc` as a fully-applied term (higher-order `rw` won't match dependent `HMul`); `⅟`→`⁻¹`
   via `invOf_eq_nonsing_inv` for integrand-usable inverses; combining-tilde `Q̃` / `φ` binder-codepoint
   hazards (use `Qt`, `phi`).
9. **sorry gate masking (lean/CLAUDE.md):** `scripts/lb` exit-0 can mask a `sorryAx` via a stale olean —
   confirm sorry-free via `#print axioms` (AxCheck.lean does this for load-bearing results); and a
   module-scoped build does NOT catch name-clashes — green-gate the FULL `lake build DLNFibre`.

---

## (d) DEAD / ruled-out — AVOID (with the one-line reason)

1. **Dyadic `|det α|`-shells / Anderson for the pivot charge** (pivchg #115, UPDATE-857): DIVERGE as a
   bound (`Σ 2^{k(m₀−1)}`). Use the front-first box-bound (effective charge `α=max{0,2c'−m₀(q−1)}`, NOT
   `m₀`). **B5a/B2 owe NO shell/Anderson AND no seam lemma** — the charge dissolves into banked machinery.
2. **`D_free = (M₁−q+1)(M_L−q+1)`** (UPDATE-859): over-estimates `D` on contracting tails, admits `c'` past
   `½·minAdm`. Use `D_prod = minAdmRec(reduced by q−1)`.
3. **The `[free-Q core] ∘ [loss IH]` factorization** (carrier-skeleton §1): INVALID — the free-core's
   `Q`-domain shrinks with `A_{≥2}` and cancels `J`'s blow-up; wrong already at `a=0`.
4. **The literal native inner (S,J) Case-1/Case-2 loop** (carrier-skeleton §5.2/5.3): needs SIX
   measure/prose repairs (triple ordinal measure, Case-1(1) label-move, `J=K_S` boundary, `S=1` base,
   Case-2-iterates, comparability-preservation). AVOID — descend by CHAIN-LENGTH / arity
   (`routeMBoxThresholdFinite_of_step`), so all six EVAPORATE.
5. **`decorated_peel_step pq/2` descent on rank-deficient `Q_b`** (`genm-sjdescent` finding, 2026-07-08,
   `[STOP+REPORT]`): UNSOUND when `Q_b` is rank-deficient. The deeper strata need the corank-Gram
   chain-length descent (B5-desc), not a blanket `pq/2` peel.
6. **`fibre_lintegral_mul_le` + `product_min_rlct` at the corner** (carrier-skeleton §B5c): give the
   boundary-wise MIN = the undershoot. Avoid at the corner (the corner blow-up ADDs, does not min).
7. **A sharp Case-2 branch for `(3,3,3,4)`** (#107): NOT needed — equal-prefix widths `M(1)=M(2)=M(3)=3`,
   coarse bound `≥ minAdm` suffices. Build the prefix-min form only for the width-general grind.

---

## CONTRADICTIONS / staleness flagged against the LIVE tree

- **`normalSlice_transfer` is NOT on canonical.** It lives on the `genm-threadedshear` feature branch with
  **3 named sorries** (`f07c06c8`); only `blockShear_step` landed clean-three there. The charge calls it
  "math-complete — grep it" — accurate for the CERT (`normalslice-cert.md`, #109 witness), but it is **not
  banked Lean.** For the vslice this is fine: LOSS finiteness uses B5-desc (chain-length descent);
  normalSlice_transfer is the COMPLEMENTARY charge-accounting side, and the vslice's accounting is instead
  delivered by the descN front-peel arithmetic (`frontPeel_binding_cut` + `frontCharge_ge_minAdm`, banked).
  **Do NOT spec normalSlice_transfer as a banked reuse for the vslice.**
- **`remaining_lt_of_support_ssubset`** (the "banked kernel" cited in carrier-skeleton §5.2/5.3 for
  termination) does **NOT exist in Lean** — it is a DESIGN spec in `reference-notes-sj-kernel.md` only. The
  actual banked termination carrier is `routeMBoxThresholdFinite_of_step` (`RouteMSJResolution:863`, arity
  strong induction), which the recommended chain-length route uses. The "banked kernel" language is stale.
- **`gammaPeelFromRedChain`** (carrier-skeleton §1 gap-tree) is a conceptual/design name — no Lean def.
- **Line drift:** `sjJointResolution` cited `:803` in carrier-skeleton; live is `:797` (def) / `:803`
  (sorry body). `sjBoundaryPeel` `:688` matches. Minor.

---

## FRESH-BUILD list — what the vslice must build that is NOT banked

1. **The single sorry `sjJointResolution` (`RouteMSJResolution:803`) — the composition.** For the `t=1`
   corank-2 chart of `(3,3,3,4)`: wire `gammaPeelIntegral` → `gammaPeelIntegral_sjGoodMap_eq'` (deep-factor
   loss form) → Schur/depth/radial (banked) → `sjSlice_corner_two_block_lt_top` (banked corner) → threshold
   `7/2`. Nodes banked; the GLUE — matching the corner brick's `h0/h1/U0/U1` hypotheses to the resolved
   chart's Jacobian powers (`3,2` → corner `6`) and the bounded-below units (via `exists_pos_lower_bound_on_sphere`)
   — is the fresh labour.
2. **★ The DEEPER-strata recursion (B5-desc) — the actual heart + the stall risk.** Inside `:803`, the
   stratum `{rank Q_b ≤ b−2}` (on `(3,3,3,4)` at `t=1`, `b=M₁−t=2` ⟹ `{Q_b=0}`, EXERCISED) needs the
   corank-Gram chain-length descent `∫ det(Q_bQ_bᵀ)^{−a/2} d(Y,A_{≥2}) →` the SHORTER-chain integral, on a
   **dominant-minor cover of `A_{≥2}`** with `J = det⁺(Gram A_{≥2})^{−b/2}` (on-chart a unit), consuming
   `hIH`. Math PROVEN (subred); the **Lean cover-assembly** (dominant-minor charts + `⅟`→`⁻¹` integrand
   conversion + no-Beta-divergence on the seam) is un-built and is where a formalisation stalls (§8-i). This
   is the highest-risk fresh piece; front-load a `local-codex-consult` on the cover-assembly finiteness.
3. **The B5b disjoint-block RLCT-add wiring** on the normal slice (`½·M₀q + ½·minAdm(reduced) =
   ½·frontCharge(q)`): consume `frontPeel_binding_cut` (banked ℕ side) + a disjoint-sum analytic bridge
   (`radial_morse_dominates_lt_top` on disjoint variable blocks).
4. **The corrected good-stratum threshold `min(tail)−b+1` wiring (NOT `q−b+1`)** — the anti-trap (c-1); the
   free-Q leaf `twoMatBox_injectiveLinear_lintegral_lt_top` is correct FOR free Q, but the descent must feed
   it the `min(tail)` budget, not the naive `q−b+1`.
