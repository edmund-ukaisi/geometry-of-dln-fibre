# recon-map.md — Lane-1 aoyagi endgame banked pieces

*Self-recon (recon1) map of the banked substrate for the three remaining Lane-1 atoms, delivered
2026-07-18 for the heart2 (#2 general-σ) build. All anchors at commit `7c3203705`
(origin/genm-lane1-shell); line numbers verified against that checkout. Paths are
`lean/DLNFibre/DLN/RLCT/Validate/…` unless marked "Core". READ-ONLY audit — nothing was edited.*

## The three target sites (the sockets heart2 fills)

- **`innerCorankDescent_lt_top`** — RouteMSJDecoratedPeelStep.lean:98. The `2≤min-corank` arm (:112)
  discharges to `hcited` (`cited_aoyagi_product_corank` def :70); the **d≤1 native sorry = :121**.
  Wiring above is sorry-free: `gammaPeelIntegral_lt_top_of_descent` :129 → `decoratedPeelStep_proof`
  :149 → `routeMBoxThresholdFinite_of_prodCorank` :167.
- **`frontCollapse_edge_b1_altu_bounded`** — RouteMSJEdgeAltuBounded.lean:1039. **α-HIGH sorry = :1068**
  (the `¬(c'<½·minAdm(redChain t M))` branch). α-LOW branch (:1067) dispatches to the LANDED
  `alpha_low_target` (:891, green). Socket has `M 1 − t = 1` (hb1), `M 0 − t < t` (haltu),
  `hb : M 2 ≤ M 1 − t` derived :1061.
- **`frontCollapseRankSector_lt_top`** — RouteMSJFrontCollapse.lean:59, **sorry :65**. a=0-bounded arm
  LANDED (`frontCollapse_wide_bounded_lt_top`); LOG / b=0 / POWER remain.

## Atom 1 — α-HIGH (KEEP corank = b=1 FreeBilinear leaf, reduce to hIH at c′−a/2)

Here a = M₀−t, b = M₁−t = 1, so `peelCharge M t = (M₀−t)(M₁−t) = a`, and the a/2 shift IS ½·peelCharge.
The α-LOW proof (`alpha_low_target` :891–1031) is the structural template — it DROPS the corank via
`freedSchurLoss_inner_bounded_le`; α-HIGH instead KEEPS it via the peel atom.

- **FreeBilinear leaf (RouteMSJFreeBilinear.lean):** `freeBilinear_box_lt_top` :117 (b=1 rank-one
  outer-product box finite up to ½·min(a+1,D+1); needs c′<½·min, T>0). Fidelity link
  `frobSq_rmatMul_corank_one` :67 (at b=1 the corank product IS the outer product); `rmatMul_corank_one`
  :60, `frobSq_outer` :49, `freeBilinear_box_factor` :77 (Tonelli split).
- **Corank-block morse peel (the "keep corank" engine):** `corankBlock_morsePeel_lt_top`
  RouteMSJCorankPeel.lean:114 (per-step finite KEEPING the ‖Q_b‖-weighted corank; needs Q_b PosDef,
  c′>pq/2, core w>0); exact-charge sibling `_eq` :65, `_setLE` :88.
  `freedSchurLoss_inner_peel_lt_top` RouteMSJFreedPeel.lean:114 = the peel already welded onto
  `freedSchurLoss` (Apiv:=0, w:=pivot energy) — **the natural α-HIGH inner engine**, but its 3 hyps
  (PosDef, pivot>0, c′>ab/2) FAIL pointwise → must be supplied as a.e./measure statements by the outer
  descent. Radial fallback: `scaledRadialEuclid_lt_top` RouteMSJEdgeScalar.lean:191 (+ `_eq` :126),
  `radial1D_lintegral_lt_top` EdgeAtoms:107.
- **Charge → hIH:** `half_minAdm_sub_half_peelCharge_le` RouteMSJDecoratedCharge.lean:67 (the exact
  c′−a/2 → hIH(redChain t M) transfer at b=1); `minAdm_le_peelCharge_add_redChain` :52 (ℕ form).
- **Edge helpers to mirror (RouteMSJEdgeAltuBounded.lean):** `edge_W_pos_ae` :810 (a.e. pivot positivity
  → supplies hpiv), `edge_J_lt_top` :694 (α-LOW landing target; α-HIGH needs a corank-charged analogue),
  `freedSchurLoss_inner_bounded_le` RouteMSJInnerDescent.lean:112 (the α-LOW DROP bound; α-HIGH replaces
  it with the peel), `outerDom_lintegral_prod` (α-LOW uses :972), `volume_shearbox_eq` :393.

## Atom 2 — a=0-POWER (general-σ determinantal resolution via det_gram ROW-RECURSION)

Template = the LANDED a=0 wide-bounded proof (`frontCollapse_wide_bounded_lt_top`
RouteMSJFrontCollapseWide.lean:187 → `frontFactor_split` + `fixedF_wide_cov_bound` →
`∫ det(F·Fᵀ)^{−M₂/2}`, closed by `front_gram_qbox_lt_top` for bounded M₂≤b). POWER (M₂≥M₁−M₀+2)
DIVERGES on that free-F Gram → use the charged/general-σ slab.

- **det_gram row-recursion:** `det_gram_cons` RouteMSJGramResidual.lean:194 (prepend a row →
  ×‖residual off span‖²; helpers :66/:89/:123); `det_gramRow` RouteMSJOffSectorB1.lean:57;
  `det_mulTranspose_eq_det_gram` RouteMSchurWishartWeight.lean:60 (bridge det(BBᵀ)→gram, entry to cons).
- **qbox core (where the recursion bottoms out):** `qbox_lintegral_lt_top` RouteMSJQBoxCore.lean:113
  (free-Q Gram-det box finite, `a<q−b+1`; proof IS the Tonelli row-recursion, consuming det_gram_cons +
  projection_rpow).
- **projection_rpow:** `projection_rpow_lintegral_uniform` RouteMSJProjRadial.lean:130 (per-row bound,
  convergence a<r≤finrank U, uniform over subspaces of dim≥r).
- **Charged general-σ slab (the POWER generalization):** `corankSlabD_charge_sint_le`
  RouteMSchurCorankSlabD.lean:560 (uniform-in-Acor bound for the CHARGED det(Acor·S·(Acor·S)ᵀ) slab;
  needs a+b≤p). Reduction target `activeGram_colBall_lt_top` :477; canonicalizers `exists_canonical`
  :374, `exists_ker_ortho_matrix` :310.

## Atom 3 — b=0 (tall-front M₁≤M₀ mirror of a=0)

Same machinery (`frontFactor_split`, `fixedF_wide_cov_bound`, residual leaf). NB `fixedF_wide_cov_bound`
RouteMSJFrontCoV.lean:185 is stated m≤n (wide) — for tall, transpose or use the column-ball leaf:
- `bRowGram_colBall_lt_top` RouteMSchurCorankSlabD.lean:159 (`a<p−b+1`); `colBallMat b p n` :150;
  `box_subset_colBall` :236 (entry-box → col-ball). `front_gram_qbox_lt_top` RouteMSJFrontCollapse.lean:152
  wraps box→colBall→bRowGram for the wide case; b=0 tall wants the transposed form.
- `det_gram_fromRows_of_orthonormal` RouteMSJFrontCollapse.lean:138 (block-Gram identity, no Cauchy-Binet);
  core `exists_ortho_complement_rows` Core/Matrix/OrthoRowComplement.lean:23.

## Negatives + landed-arm audit

- ⚠ **`deeperFlag_waist_a0` / `deeperFlag_waist_b0` DO NOT EXIST** as landed theorems — only NAMED as
  future atoms (RouteMSJDecoratedPeelStep.lean:113-120) + routed to a separate SVD-qPeel base ("task #156").
  Do not plan to consume them.
- Only 5 `frontCollapse*` theorems exist: `frontCollapseRankSector_lt_top` (sorry atom, FrontCollapse:59),
  `frontCollapse_wide_bounded_lt_top` (**a=0 bounded LANDED**, FrontCollapseWide:187), and 3 edge theorems
  (EdgeAltuBounded): `edge_frontCollapse_consFront_lt_top` :419, `edge_frontCollapse_cleanBox_lt_top` :495,
  `frontCollapse_edge_b1_altu_bounded` :1039 (α-HIGH sorry). **NO LOG, NO b=0, NO POWER standalone landed.**
- LOG building blocks (RouteMSJEdgeAtoms.lean): `one_add_log_inv_le_rpow` :71 (log → small negative power),
  `sigmaLog_integral` :129, `one_add_sigmaLog_le_rpow` :139.
- Skeleton driver (sorry-free above the holes): `gammaPeelIntegral` RouteMSJResolution.lean:517;
  `sjBoundaryPeel` :688; `DecoratedPeelStep` RouteMSJDecoratedRec.lean:78;
  `routeMBoxThresholdFinite_of_decoratedPeel` :99.

## Key charge / structure defs (verbatim anchors)

- `redChain t M := Fin.cons t (fun i => M i.succ.succ)` RouteMLayerSplit.lean:40 (one shorter, head=t).
- `minAdm` :51 / `minAdmRec` :58 (L=0→0, L=1→M₀·M₁, else inf over cuts).
- `peelCharge M u := (M 0 − u)*(M 1 − u)` RouteMSJDecoratedCharge.lean:45.
- `tailChain M := fun i => M i.succ` RouteMSJResolution.lean (α-LOW writes it inline).
- `RouteMBoxThresholdFinite M := ∀ c', (c':ℝ)<minAdm M/2 → routeMLayerBoxIntegral M c' 1 < ⊤`
  RouteMBoxReduction.lean:165; `routeMLayerBoxIntegral` :62; `paramsBoxM` :56.
- `freedSchurLoss x Γ Q := frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ + Γ·Q_b)` RouteMSJChartShear.lean:146
  (P=of x.1.1, Q̃ₚ=Q.inl+P⁻¹·(of x.1.2)·Q.inr); `schurShift` :139; `outerDom` :185; `SJOuter` :56.
