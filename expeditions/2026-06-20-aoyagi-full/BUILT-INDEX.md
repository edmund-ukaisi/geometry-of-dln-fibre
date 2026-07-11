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
  identity `frobSq(A₀·Q)` → `‖A·Q̃ₚ‖² + ‖C·Q̃ₚ+Γ·Q_b‖²` (§5 Step-3), the `L=2` seed.
- **★ OPAQUE-WIDTH Schur split + Γ-freeing shear — BANKED (B2/B5a′ LANDED, genm-sjcarrier6/7; verified
  2026-07-11, supersedes the stale "opaque-width lift owed" in peel-buildplan §2.2/§4.2):**
  - `frobSq_rmatMul_reindex` (`RouteMSJBlockReindex:71`) — raw loss = block-matrix loss (flat→block coords).
  - `chartInner_blockReindex_eq_of_emb` (`RouteMSJBlockReindex:256`) — raw opaque-width chart integral →
    block coords, `blockSplitEquiv`-instantiated ∀`(ρ,κ)`.
  - `frobSq_schur_split_inv` (`RouteMSJChartWeld:83`) — POINTWISE opaque-width Schur split (`⁻¹` form,
    integrand-usable; hyp `IsUnit M'.toBlocks₁₁`). Aoyagi Lemma-2, exact.
  - `chartInner_schurWeld_eq_of_emb` (`RouteMSJChartWeld:149`) — the composed weld = B2/B5a′ verbatim:
    `∫ frobSq(rmatMul A₀ Q)^{−c'}` over `matBox ∩ pivotChart ρ κ` → the Schur cross-coupled block integral
    with Γ exposed (= `gammaPeelIntegral`'s inner integral, p=M₀,n=M₁,T=1).
  - `chartInner_schurShearFree_eq` (`RouteMSJChartShear:253`) — the block-shear (B5a′ proper): the `D↦Γ`
    MP shear frees Γ as an INDEPENDENT variable over the shear-image box; `freedSchurLoss` = Γ-free pivot
    `frobSq(P·Q̃ₚ)` + corank `frobSq(C·Q̃ₚ+Γ·Q_b)`. All three: clean-three, wired `DLNFibre.lean:798/805/820`.
- `RouteMSJSphereBlowup` (0-sorry) — the polar blow-up CoV.
- `RouteMSJPivotChart` (0-sorry): `measurePreserving_shearSub` (`:337`) — the MP shear `D↦Γ=D−CA⁻¹B`.
- `RouteMSJCorankPeel` (0-sorry): `corankBlock_morsePeel_lt_top` (`:114`) — the corank-block radial Morse
  peel (the det-Jacobian atom `u₀²U₀+u₁²U₁ → det(Q_bQ_bᵀ)^{−a/2}·…`).
  **★ ATOM ADJUDICATION (ADJUDICATED 2026-07-11, peel-buildplan §2.1; three decorrelated lines — exact read,
  pure-vs-atom-adj, Codex xhigh):** `corankBlock_morsePeel` is the native §5 atom **ONLY on the FULL-RANK
  `Q_b` strata (good `rank=q` / top `rank=q−1`)** — it needs `hG : (Q_bQ_bᵀ).PosDef`, delivering the exact
  shift `c'↦c'−pq/2` with a FINITE weight there. **CONSUME for B3/B4.** On the deeper stratum
  `rank Q_b = r < q` the map `Γ↦Γ·Q_b` has a `p(q−r)>0`-dim kernel, so the enlarged full-space integral is
  `+∞` throughout the ENTIRE true box-finite range (exact witness: `∫_ℝ(x²+y²γ²)^{−c}dγ = K_c|y|^{−1}|x|^{1−2c}`,
  outer `y`-integral diverges). **Do NOT consume `corankBlock_morsePeel` on B5 (the deeper strata, ~86%).**
  The "det ledger" the operator brief names is §5's **det-1 UNIT clears (`frobSq_schur_block_split` /
  `block_elimination`) + the `diag(b)` MONOMIAL ledger — NOT `det(Q_bQ_bᵀ)`.** The native deeper-stratum atom
  is the **in-box radial blow-up + shared monomial ledger** (≡ subred's chain-length descent on the shorter
  chain). (Supersedes the earlier "assess whether to consume" caveat — now adjudicated: full-rank only.)

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
2. **DIRECT Aoyagi §5 coupled diag(b) peel** (the paper's method, operator-opened 2026-07-11): prove the
   coupled peel directly via §5's recursion, consuming the scaffold above. Thread: `threads/genm-sj5/`.
   **BUILD-PLAN (2026-07-11): `threads/genm-sj5/peel-buildplan.md`** — TRUE + BOUNDED, no wall (3
   decorrelated lines). Key results:
   - **Target reframe: prove `DecoratedPeelStep` (`RouteMSJDecoratedRec:78`), NOT `803` directly.** The
     banked driver `:99` closes `(□)` from it AND `:111` retro-fills `803` — so `803` is obsolete once
     `DecoratedPeelStep` lands. It is provable via the DOUBLE induction (the earlier "DecoratedPeelStep
     unprovable" was the plain-IH SINGLE peel; the double induction proves it).
   - **Shape: double induction.** OUTER = chain arity (BANKED, `routeMBoxThresholdFinite_of_step`). INNER =
     the decorated resolution within one peel, terminating by **chain-length descent (subred)**, NOT Aoyagi's
     literal two-index `(S,J)` loop — a deliberate design call: the descent has measure `= L` (banked) and
     **all six of the literal loop's prose repairs evaporate**.
   - **DAG + commission order (§4.2), UPDATED 2026-07-11:** B4 (CERTIFIED, banked) → **B5a′ LANDED** (the
     opaque-width Schur split + Γ-freeing shear are BANKED, genm-sjcarrier6/7 — see the OPAQUE-WIDTH row
     above; genm-sj5-schur STOPPED report-only, #124 done) → **B5-desc — THE SOLE REMAINING CONTENT** (the
     deeper-strata corank-Gram integral finiteness). Skeleton IN FLIGHT (`genm-sj5-schur`, #125/#126,
     statements-first, isolating the hole `innerCorankDescent_lt_top`).
   - **★ COVER-SEAM DE-RISK COMPLETE (2026-07-11, `genm-sj5-cover`, `threads/genm-sj5/cover-derisk.md`) —
     NO WALL; the flagged risk (§4.4) is CLEARED, twice over.** Exact algebra (sympy CoV identity
     `QQᵀ=Q_S W Q_Sᵀ` + Cauchy–Binet dominance, 0/20k violations) + decorrelated Codex concurring term-for-term:
     the seam is Lebesgue-null, partition = indicator-mult (no boundary term), transition Jacobian `=1` exactly
     on the seam, integrand `O(1)` there; the `|det A_S|^{−b}` det-inverse is exactly cancelled by the
     shrinking image `vol=2^{bm}|det A_S|^b` (the `s⁻¹` pole is a FULL-SPACE artifact the box never has).
   - **★ THE FILL ROUTE (CORRECTED 2026-07-11 by the bridge de-risk #128 — the Γ-first majorant is a TRAP).**
     ❌ **OFF-ROUTE (do NOT use):** "integrate Γ first → det-Gram `I(a)=∫det(Q_bQ_bᵀ)^{−a/2}` → m-column
     majorant → banked `detGram_lintegral_lt_top`". The bridge de-risk (`bridge-derisk.md`, exact SVD +
     decorrelated Codex) proved this is **+∞ on the pivot-degenerate locus `{w=0}`** for `c'∈[p·b/2, ½minAdm)`
     (`=[2,7/2)` for (3,3,3,4)): on `{w=0}` the inner Γ-integral is `∫‖ΓQ_b‖^{−2c'}`, finite only iff
     `c'<p·b/2=2 < 7/2`. Any Γ-first-then-deeper route inherits it. `corankGram_box_lt_top` (I(a)) is
     true-but-OFF-ROUTE — the hole does NOT reduce to it. The pivot `w` is LOAD-BEARING (sector bound
     `min{w^{−c'},E^{−c'}}`). `corankBlock_morsePeel`/`freedSchurLoss_inner_peel` need PosDef+pivot>0+c'>ab/2
     POINTWISE — hold only on `{w>0}`, fail on `{w=0}`.
     ✅ **CORRECT — the FRONT-FIRST JOINT bound:** (1) RECOMBINE `(x,Γ)→A₀` (banked MP+reversible shear
     `chartInner_schurShearFree_eq`/`measurePreserving_shearSub`) — integrate pivot+Γ TOGETHER; (2) ★ **the ONE
     new brick** — front-first box-exponent `g(Q)=∫_{A₀-chart}frobSq(A₀·Q)^{−c'} ≤ C·σ_q(Q)^{−α}`,
     `α=max{0,2c'−M₀(q−1)}` (covdesign §CONCESSION), CONSUMING banked spectral: `RouteMSJFrontSpectral`
     (`frobSq_mul_eq_sum_eigenvalues`, `sigMin_sq_eq_iInf_eigenvalues`, `collapseIndex_le`),
     `RouteMSJProductTube` (`sigMin`, `det_gram_le_sigMin_sq_mul_trace_pow`, `sigMin_rpow_le_det_rpow_of_mem_box`),
     `RouteMSJTwoBlockRadial.twoBlock_radial_le` — NOT yet banked as a single lemma (genm-sj5-schur build-scanning);
     (3) `∫_{A'}σ_q^{−α}` against the tube codim `D=minAdm(reduced)`, BANKED: `minAdm_eq_frontPeel` + #127 + Core.
     `c'<½minAdm ⟹ α<D` strict ⟹ finite. **★ THE TWO LANES CONVERGE on this one brick** — lane-1's banked
     spectral machinery is now on the §5 critical path, but the §5 fill stays cheap (skeleton pre-banked the rest).
   - **det-monotone (`RouteMSJDetMono`, banked @1e806282 unwired):** the #112 rebuild (`det_le_det_of_posSemidef_sub`)
     — reusable/Mathlib-worthy, but NO LONGER on the §5 critical path (it was the OFF-ROUTE majorant's tool).
     Keep for reuse. (#112 was LOST — cbmin worktree gone — hence the rebuild.)
   - **∀M product-tube codim `D` CLEARED (#127, `prodD-general.md`):** `D=C(reduced)=minAdm(reduced)` via the
     paper's add-longest thm + rank-shift + QIP, CONSUMING banked Core (`cCodim_rankShift`,
     `productRankLocusLE_eq_iUnion_orbitRankLocus`, `cCodim_eq_qipMin`); leading power `=codim` (affine-on-β-simplex
     vertex + `normalSlice_transfer` #109). `L=D` is the reduced chain's box-finiteness one arity down — FOLDS
     INTO the recursion, not a new build. WATCH (Lean bookkeeping): `minAdm=cCodim` bridge + real-vs-complex seam.
   - **CENTER-LIST level-separated:** the proportionality center `(x₂,p₂)∥(x₃,p₃)` is Level-B (θ-count) — not
     needed for the front-first FINITENESS route. Reserve for a Level-B resolution.
   - **Atom note:** `corankBlock_morsePeel_setLE` (the det-Gram atom) is native on full-rank strata only; on
     bottleneck charts (`Q_bQ_bᵀ` PosDef fails) the majorant route replaces it. (Correction: `mulLeftₚ`/
     `lintegral_comp_mulLeftₚ` are for the DOWNSTREAM absorption Jacobian, NOT the shear.)
   - **Most likely to break (§4.4):** the det-inverse dominant-minor cover SEAM — the per-chart bound the
     banked `RouteMSJDominantCover` assembly consumes as a hypothesis (Beta-divergence on a cell boundary,
     the atom-route failure mode). Being de-risked on the `(3,3,3,4) q∈{1,2}` slice before B5-desc.
   - **Already banked (index reconciliation, do NOT re-derive):** B5-desc-ℕ descent arithmetic
     (`RouteMSJDescNat.lean`, `frontPeel_binding_cut : ∃q≤tailMin M, minAdm M = frontCharge M q`, #117 —
     anti-trap `tailMin−b+1 ≠ minAdm`, composition IS the front-peel); the cover-ASSEMBLY
     (`RouteMSJDominantCover`, #118, reviewed); the pivot-charge finiteness (front-first box-bound, α =
     max{0,2c'−m₀(q−1)}, linchpin `minAdm ≤ D+m₀(q−1)`, #115 — the dyadic shell is DROPPED, owes no shell
     lemma). The genuinely-owed content = B5a′ (identity lift) + B5-desc (the inner induction + deeper descent).

## HOUSEKEEPING TODO
- [x] (1) DONE @02323c4d — the stale `RouteMSJResolution.lean` docstrings (`:57/:69/:92/:674/:946`,
  "two sorries"/"WALL"/"this named sorry") corrected to "one remaining sorry (`sjJointResolution:803`);
  `sjBoundaryPeel` CLOSED sorry-free". Green-gated (8304 jobs), sorry count unchanged (only `:803`).
