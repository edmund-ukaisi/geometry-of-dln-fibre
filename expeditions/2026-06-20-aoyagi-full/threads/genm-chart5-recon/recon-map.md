# recon-map — chart-5 big-cell CoV (`RouteMSJIncidenceChart5BigCell.lean`)

**Thread `genm-chart5-recon`, self-recon (read-only). Date 2026-07-15.** No Lean edits, no build.
Maps our OWN banked state for the determinantal big-cell CoV of the incidence resolution
(`genm-incidencepp/incidence-cert.md` §3b(5) + §3b(b)): `W ↦ (W₁₁,W₁₂,W₂₁,E)`,
`E := W₂₂ − W₂₁ W₁₁⁻¹ W₁₂` (Schur), `W₁₁ ∈ GL_ℓ`; facts `|det DΦ| ≡ 1`, `rank W = ℓ + rank E`,
`{rank W ≤ ℓ} ∩ chart = {E=0}`, rank-`s` `Y`-block chart, radial `∫₀^δ r^{C_{ℓ,s}−1−2q}dr`, `(I,J)`
minor atlas.

Paths are relative to `lean/`. brickdcont/brickdbuild pieces are on the tide branches
`origin/genm-sj5-brickd{cont,build}` (NOT yet merged to `expedition/aoyagi-full`) — flagged per item.

---

## HEADLINE (what to reuse / what's staged / what's genuinely new)

**The one thing the controller must know: the "genuinely-new content" the charge worried about — the
block-LU rank identity `rank W = ℓ + rank E` and `{rank W ≤ ℓ} = {E=0}` — is ALREADY FULLY BANKED,
sorry-free, in `DLNFibre.Core`, in exactly the cert's nonsing-inverse form.** It is not a gap.

- `rank W = ℓ + rank E` **=** `Core.SchurChartIff.rank_fromBlocks_invertible₁₁`
  (`DLNFibre/Core/SchurChartIff.lean:41`): `(fromBlocks Δ B12 B21 B22).rank = r + (B22 − B21·Δ⁻¹·B12).rank`.
- `{rank W ≤ ℓ} = {E=0}` **=** `Core.SchurChartIff.rank_le_iff_schur_eq` (`:64`):
  `(fromBlocks Δ B12 B21 B22).rank ≤ r ↔ B22 = B21·Δ⁻¹·B12` (i.e. `E = 0`). Exact-rank form `:81`.
- Both rest on OUR OWN Core primitives (block-diag rank additivity `Matrix.rank_fromBlocks_zero_offdiag`
  + `Matrix.rank_eq_zero_iff`, `RankNormalFormDim.lean:78,44`) — these are **not** in stock Mathlib
  v4.29; we built them. Do not re-derive; do not re-declare a third copy (see PITFALL name-clash).

So the chart-5 build is **measure/CoV/atlas plumbing over a fully-banked algebraic core**. The
remaining genuinely-new labour (GAP list) is: (i) instantiate the CoV engine on the specific
translation-in-`W₂₂` map with `|det|≡1`; (ii) the `(I,J)`-minor→top-left permutation CoV (Jacobian ±1);
(iii) glue the finite minor atlas with null overlaps. All three have banked templates named below.

---

## (a) CONSUME — banked, sorry-free, on `expedition/aoyagi-full`; call it

### A1. The block-LU / Schur rank core (the cert's §3b(b), DONE)
- **`Core.SchurChartIff.rank_fromBlocks_invertible₁₁`** `SchurChartIff.lean:41` — `rank = r + rank(Schur)`,
  `Schur = B22 − B21·Δ⁻¹·B12`, hyp `IsUnit Δ.det`. **This is `rank W = ℓ + rank E` verbatim.**
- **`Core.SchurChartIff.rank_le_iff_schur_eq`** `:64` — `rank ≤ r ↔ B22 = B21·Δ⁻¹·B12`. **`{rank W ≤ ℓ}={E=0}`.**
- **`Core.SchurChartIff.rank_eq_iff_schur_eq`** `:81` — `= r` form.
- Underlying primitives (also directly usable):
  - **`Matrix.rank_fromBlocks_zero_offdiag`** `RankNormalFormDim.lean:78` — `(fromBlocks A 0 0 D).rank = A.rank + D.rank` (Fin-indexed, over a field). Built by us.
  - **`Matrix.rank_eq_zero_iff`** `RankNormalFormDim.lean:44` — `M.rank = 0 ↔ M = 0`. Built by us.
  - **`Core.rank_diagonal_indicator_lt`** `RankNormalFormDim.lean:27` — `rank diag(I_r,0) = r` (if the atlas ever needs the normal-form value).

### A2. The set-level chart bijection + dimension (parallel Core development)
- **`Core.DeterminantalChart.pivotRankChartEquiv`** `DeterminantalChart.lean:181` — explicit bijection
  `{M ∈ pivotRankChart} ≃ {Δ // IsUnit Δ.det} × Mat × Mat`, `B22` Schur-forced. The set-level chart map;
  reuse if chart 5 wants the bijection rather than the raw rank iff.
- **`Core.DeterminantalChart.pivotRankChart`** `:172` — the det-open chart `{rank = card·∧ IsUnit toBlocks₁₁.det}`.
- **`Core.DeterminantalChart.rank_fromBlocks_eq_card_iff_schur_inv`** `:158` — general-index `= card m` iff (`Δ⁻¹` form).
- **`Core.DeterminantalChart.rank_fromBlocks_eq_card_iff_schur`** `:125` — same, `⅟Δ` form.
- **`Core.DeterminantalChart.rank_fromBlocks_zero`** `:75` — general-index block-diag additivity
  (the `Fintype`/general twin of `rank_fromBlocks_zero_offdiag`; use whichever index shape fits).
- Dimension cross-check: **`finrank_pivotRankChart_params`** `:221`, **`dim_params_eq_delta`** `:232`
  (`r² + r(q−r) + (p−r)r = r(p+q−r)`) — for the codimension bookkeeping / bedrock non-vacuity.
- **`Core.SchurRankZero.schur_complement_zero_of_rank_le`** `SchurRankZero.lean:34` — one-direction
  `rank ≤ r ⟹ B22 = B21·⅟B11·B12` (column-space proof; `⅟` form). Subsumed by `rank_le_iff_schur_eq`
  but available if an `Invertible` instance is already in hand.

### A3. The CoV engine idiom (item-1 of the charge)
- **`RouteMNullSliceCov.ldu_cov_of_differentiable_injOn`** `RouteMNullSliceCov.lean:64` — the
  chart-agnostic image-pushforward CoV engine. **Copy this idiom.** Its skeleton (all reusable):
  - core call `lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hFDeriv hInj g`;
  - **3 obligations, none from the det value alone** (charge item 1): `HasFDerivWithinAt` (from a global
    `Differentiable ℝ φ` via `(hdiff x).hasFDerivAt.hasFDerivWithinAt`); `Set.InjOn φ S`;
    the abs-det value substituted by `setLIntegral_congr_fun` + `habsdet`;
  - **null-slice add-back** (image of a null set is null): `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`
    + `setLIntegral_congr` (`ae_eq_set`) on the LHS, `MeasureTheory.diff_ae_eq_self` on the RHS;
  - coordinate-hyperplane measurability: `measurableSet_eq_fun (measurable_pi_apply p) measurable_const`;
    finite-union nullity `MeasurableSet.biUnion` + `measure_biUnion_null_iff`.
  - **For chart 5 the Jacobian is `≡ 1`** (translation in `W₂₂`), so `habsdet` collapses to `= 1` — a
    strictly simpler instantiation than this file's `∏|u_j|^{h_j}` template.
- (`RouteMInteriorLDUCov.lean:80` holds a pre-extraction copy of the same engine; the standalone home is
  `RouteMNullSliceCov`. Import the latter.)

### A4. Matrix-space CoV over the raw pi type (the pi-diamond workaround, item-1 continued)
Chart 5's map is a **block-affine** map on matrix space; the recurring `Matrix.module` vs
`NormedSpace.toModule` diamond (lean/CLAUDE.md) is already dodged by the banked pi-transcription:
- **`RouteMSJDecoratedPeelMeas.mulLeftₚ`** `RouteMSJDecoratedPeelMeas.lean:37` — left-mul as a `LinearMap`
  on the RAW pi type `(Fin c → Fin t → ℝ)`, column-indexed (`LinearMap.pi` of per-column `K.mulVecLin`).
- **`det_mulLeftₚ`** `:51` — `LinearMap.det (mulLeftₚ c K) = (det K)^c` (via `LinearMap.det_pi`).
- **`lintegral_comp_mulLeftₚ`** `:69` — full-space CoV, `∫ g(K·Y·) = ofReal(|det K|^c)⁻¹ · ∫ g`.
- **`lintegral_box_le_absorption`** `:90` — the **affine** (mul + translation) box bound
  `∫_box g(P·X· + S·) ≤ ofReal(|det P|^c)⁻¹ · ∫ g`, translation via `lintegral_add_right_eq_self`.
  Chart 5's translation-in-`W₂₂` is the `P = 1, S = W₂₁W₁₁⁻¹W₁₂`-shaped affine map → this is the template.

### A5. det = 1 for a shear / translation (item-2 of the charge)
- **`ParamsReshapeMP.continuousLinearMap_abs_det_eq_one_of_measurePreserving`** `ParamsReshapeMP.lean:98`
  — a measure-preserving continuous linear self-map has `|det| = 1`. Use if going the measure-preserving route.
- **`RouteMLayerCoverGEL2.shear334Deriv_det`** (in `RouteMLayerCoverGEL2.lean`) — a **worked shear det = 1**
  via `Matrix.BlockTriangular.det` (unipotent `I + N`, unit diagonal). The direct route for chart 5's
  `|det DΦ| = 1`: the derivative is block-unipotent, det = 1 by `Matrix.det_fromBlocks_zero₂₁`/`BlockTriangular.det`.

### A6. Radial finiteness (item-4 of the charge) — the `∫₀^δ r^{C_{ℓ,s}−1−2q}dr` gate
- **`RouteMSJRadialPolar.lintegral_Ioc_rpow_lt_top`** `RouteMSJRadialPolar.lean:157` —
  `∫_{Ioc 0 R} r^e < ⊤` for `e > −1`. **THE exponent gate**: `C_{ℓ,s}−1−2q > −1 ⟺ 2q < C_{ℓ,s}`.
- **`RouteMSJRadialPolar.corner_block_lintegral_lt_top`** `:185` — `∫_{ball} g^{−c'} < ⊤` for a
  degree-2 homogeneous `g` bounded below on the sphere, `c' < N/2`. The corner-cell finiteness.
- **`RouteMSJRadialInt.lintegral_norm_rpow_neg_ball_lt_top`** `RouteMSJRadialInt.lean:89` —
  `∫_{ball} ‖x‖^{−a} < ⊤` for `a < n` (multi-dim radial). Companion `integrableOn_norm_rpow_neg_ball`.
- **`RouteMSJTwoBlockRadial.twoBlock_radial_le`** — the two-block radial (the corner's `w_Y·w_W` double radial).
- **`RadialResidualPower.radial_morse_residual_power_le`** — residual-power bound, `(m+1)/2 < c'`.
- **`RouteMSJProjRadial.projection_rpow_lintegral_uniform`** — projection radial, uniform over minors.
- **`RouteMSJSphereBlowup.lintegral_eq_polar` / `lintegral_eq_sphereProd`** — the polar/sphere-product
  decomposition feeding the radial integrals.

### A7. Perm-Jacobian / WLOG-to-top-left (item-2, the `(I,J)` atlas)
- **`HeadlineColPermWLOG.headline_frontPivot_exists`** — existence of the pivot permutation
  `P : Equiv.Perm (Fin ·)` (front-pivot WLOG). The `(I,J)`-minor→top-left reindex uses this;
  the perm-CoV Jacobian `±1` on `W`-space is a small wrapper (see GAP G2).
- `RouteM4422.lean` / `Case222NodeDescent.lean` carry reindex/`submatrix`-perm CoV idioms to crib.

---

## (b) STAGED — built for exactly this point (on brickdcont/brickdbuild; NOT yet merged)

### B1. Piece (i) — the chart algebra `RouteMSJIncidenceChart.lean` (258 lines, `origin/genm-sj5-brickdcont`)
Deliberately built to feed chart 5. Sorry-free (per docstring); axiom-clean claimed — builder must
`#print axioms`-confirm after merge. Key theorems (all `DLNFibre.DLN.RLCT`, `Matrix` over `ℝ`):
- `fromCols_mul_transpose`, `chartGram_congr`, **`det_chartGram`** (`det(Qb Qbᵀ) = (det D)²·det(I+XXᵀ)`),
  `pushThrough` (Woodbury), `chartSwap`, `chartNull_Qb`/`chartNull_Qp`/`chartNull_gram`,
  `chartProj_Dcancel`, `chartProjRed_block`, `chartProjComplement` (`I−Π_b = N(NᵀN)⁻¹Nᵀ`),
  **`transverseSchurGram`** (`Qp(I−Π_b)Qpᵀ = W(I+XᵀX)⁻¹Wᵀ`). Imports `RouteMSJPivotBlowup` (on-branch).
- (brickdbuild's copy is a 128-line subset; consume brickdcont's fuller version.)

### B2. Piece (iv) — the exponent certificate `RouteMSJIncidenceExponent.lean` (97 lines, `origin/genm-sj5-brickdcont`)
The `C_{ℓ,s}` arithmetic. Sorry-free (per docstring). Consume the **per-stratum gate** freely:
- **`clsCodim M u ℓ s`** — `= u(M₁−u) + M₀ℓ + (M₀−s)(u−ℓ−s) + s((M₂−(M₁−u))−ℓ)`.
- **`clsCodim_add_ab_eq`** — the `ℓ`-independence ring identity `C_{ℓ,s} + ab = (M₀−s)(M₁−s)+sM₂`.
- **`clsCodim_gate`** — `minAdm M ≤ C_{ℓ,s} + ab` (so `q < T1_q ⟹ q < C_{ℓ,s}/2`, each stratum finite).
- **`minAdm_arity3`**, **`minAdm_le_ab_add_uM2`** (comparator gate `T1_q ≤ uM₂/2`).
- **⚠ SCOPE — do NOT over-consume (see DEAD D4):** the per-stratum gate is proven; the **aggregate**
  "min over the `(ℓ,s)` range = 2·T1" (i.e. that the enumeration is COMPLETE) is **gated on `genm-bltj`**
  (the `b<j` / `Q_p`-degeneration completeness question). Build the per-stratum bound; do not claim full
  coverage as canonical until bltj confirms.

### B3. Surrounding brickd context (also on brickdcont; for import-wiring awareness)
`RouteMSJPivotDom.lean` (162), `RouteMSJPivotFin.lean` (1333), `RouteMSJHeadSplitDom.lean` (287),
`RouteMSJDeeperFlagCore.lean` (edited). These are the pivot/head-split domination the chart 5 estimate
plugs into; not chart-5 CoV internals, but the consumers whose interface chart 5 must match.

---

## (c) LESSONS / pitfalls that bite chart 5

1. **The matrix-CoV pi-diamond (`Matrix.module` vs `NormedSpace.toModule`) — the top hazard**
   (lean/CLAUDE.md). A `LinearMap` built over `Matrix.module` won't unify with the Haar CoV lemma.
   **Fix (already banked, A4): transcribe the chart map over the raw pi type `Fin c → Fin t → ℝ`,
   column-indexed** (`mulLeftₚ` pattern); det factors via `det_pi`. Do NOT build chart 5's CoV as a
   `Matrix →ₗ Matrix` map.
2. **`⅟` (invOf) vs `⁻¹` (nonsing_inv).** The cert's `E = W₂₂ − W₂₁ W₁₁⁻¹ W₁₂` uses `⁻¹`. Consume the
   `⁻¹`-form lemmas (`rank_fromBlocks_invertible₁₁`, `rank_le_iff_schur_eq`, `rank_fromBlocks_eq_card_iff_schur_inv`)
   to stay integrand-usable; bridge any `⅟`-form with `invOf_eq_nonsing_inv` (after `IsUnit.invertible`).
3. **Sorry-masking olean.** `scripts/lb` exit-0 can mask a `sorryAx` via stale cache. Confirm chart 5 (and
   the freshly-merged brickdcont pieces) axiom-clean with `#print axioms` / `AxCheck.lean`, not exit status.
4. **`scripts/lb <Module>` misses name clashes with siblings.** Two block-diag-additivity lemmas already
   coexist (`Matrix.rank_fromBlocks_zero_offdiag` in `RankNormalFormDim` vs `Core.rank_fromBlocks_zero` in
   `DeterminantalChart`) and two `rank_eq_zero_iff` (`_root_.Matrix.rank_eq_zero_iff` vs
   `Core.rank_eq_zero_iff`) — different names, no clash, but **do NOT introduce a third copy**. Green-gate
   the FULL `lake build DLNFibre`, and reuse rather than re-declare.
5. **Fin opaque-width matrix-apply "no progress" in-context** (lean/CLAUDE.md). If chart 5 works with block
   indices `Fin ℓ ⊕ Fin (u−ℓ)` at dependent widths, `mul_apply`/`cons_val_*` may not fire after
   `ext`/`fin_cases`; prove entries as `have`s at explicit `⟨_, by decide/omega⟩` and `exact` in.
6. **Bedrock / non-vacuity.** Show the chart-5 result with a witness in-file — the cert's `(2,2,3)` corner
   `ℓ=0` cell (`DeterminantalChart` already carries a `(2,2,2) r=1` witness at `:246`; a `(2,2,1)`-minor
   witness fits chart 5). Name the theorem for what it proves (a per-cell CoV/exponent, not the aggregate).

---

## (d) DEAD / ruled-out — do NOT re-explore (from `incidence-cert.md`)

1. **Pointwise-in-`z` domination is FALSE** (§Verdict-1). A rank-dropping `Qp` gives `δ^{5−2q}` blow-up
   (`(3,3,5)@u=2`, `q>5/2`) while `‖Qp‖²≍1`. The estimate is **INTEGRATED** — resolve `(z,A_cor,front)`
   jointly. A chart-5 bound built to hold per-`z` will thrash on a false wall.
2. **Dropping the scope `a+b ≤ M₂`** (§Verdict-2). Off-scope the corank-Gram
   `∫ det(Qb Qbᵀ)^{−a/2}` DIVERGES (`(3,3,3)@u=1,a=b=2`). Thread the scope hypothesis.
3. **Pulling det-Gram out uniformly (`sup_{A_cor}`)** (§4). `sup det(Qb Qbᵀ)^{−a/2} = ∞`; it must ride
   INSIDE the incidence tube (the shrinking indicator is part of the monomialisation). Keep det-Gram coupled.
4. **Treating "min `C_{ℓ,s}` over the `(ℓ,s)` index = 2·T1" as canonical coverage** (cert §3 controller
   caveat + B2). The min is over the ENUMERATED strata; index-completeness in the `b<j` regime is under
   live adjudication (`genm-bltj`). Per-stratum gate = sound; aggregate coverage = gated.
5. (θ-count/other-thread dead routes in lean/CLAUDE.md — merge-up corner-raise, single-vertex strict mono,
   Route A `Φ` — are unrelated to chart 5; ignore.)

---

## GAP — genuinely-new chart-5 labour (with banked templates)

The block-LU algebra is DONE (headline). The fresh labour is plumbing, each with a named template:

- **G1. The specific chart-5 CoV map `Φ` with `|det DΦ| ≡ 1`.** No banked lemma is this exact
  translation-in-`W₂₂` map. Instantiate the A3 engine (`ldu_cov_of_differentiable_injOn`) with
  `habsdet = 1`; get differentiability + `InjOn` on `{det W₁₁ ≠ 0}` from the explicit inverse
  (`E = W₂₂ − W₂₁W₁₁⁻¹W₁₂` recovers `W₂₂`); realise the map over the raw pi type (A4) to dodge the
  diamond; `|det| = 1` via A5 (`BlockTriangular.det` on the unipotent derivative). **Bounded** — all
  ingredients banked.
- **G2. The `(I,J)`-minor → top-left permutation CoV (Jacobian `±1`).** `rank_le_iff_schur_eq` is stated on
  `fromBlocks Δ …` (top-left pivot); the general minor needs a permutation reindex on `W`-space with a
  measure-preserving `±1` Jacobian. `HeadlineColPermWLOG.headline_frontPivot_exists` gives the perm's
  existence; the perm-CoV wrapper (permutation matrix is measure-preserving / `rank_reindex`,
  `rank_submatrix` for the rank side) is a small fresh lemma. Cross-check `RouteM4422`/`Case222NodeDescent`
  reindex idioms first.
- **G3. Finite-minor atlas gluing with null overlaps.** Finitely many `(I,J)` minors cover
  `{rank Qb=b} × {rank W=ℓ}`; lower-corank strata are null in the closure. A3's engine gives the
  single-chart null-slice add-back (`addHaar_image…null` + `ae_eq_set`); the multi-chart cover/glue
  (finite union, pairwise-null overlaps) is fresh but standard — no abstract resolution framework needed
  (cert §3b: "the stratification IS a finite union of explicit big-cells").

None of G1–G3 is new *mathematics*; each is bounded measure-theory/reindex plumbing over banked pieces.
The build's risk is entirely in the DEAD-list traps (integrated-not-pointwise, scope, coupled det-Gram),
not in missing lemmas.

---

## Verification notes (for the controller / builder)
- All `(a)` Core files are on `expedition/aoyagi-full`, `sorry`/`axiom`/`native_decide`-free by `rg`, and
  imported in `DLNFibre.lean`. Axiom footprint of the load-bearing lemmas should be confirmed via
  `#print axioms` / `AxCheck.lean` after any downstream edit (sorry-masking-olean gate).
- All `(b)` pieces are on `origin/genm-sj5-brickdcont` only — chart 5 must either branch off brickdcont or
  await its merge. Re-confirm sorry-free + axiom-clean at merge (docstrings claim it; not independently built here).
- `Matrix.rank_fromBlocks_zero_offdiag` and `Matrix.rank_eq_zero_iff` are **our** `_root_.Matrix`
  additions (`RankNormalFormDim.lean`), not stock Mathlib v4.29 — a contradiction with any note that
  assumes them Mathlib-native. They are real and sorry-free; just ours.
