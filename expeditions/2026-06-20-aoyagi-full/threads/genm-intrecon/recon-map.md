# genm-intrecon — self-recon map: the interior h_int arm's terminal obligation

**Seat:** self-recon (read-only). **Date:** 2026-07-16. NO Lean edits/builds/commits.
**Refs swept:** `origin/genm-integration` @6e7691a96 (the mountain-composition files live HERE),
`origin/genm-corankrec` @a070b639a (the full QIP family + interface), `origin/tide/genm-intcell`
@6efdfface (the atom RadialCriticalPower; built directly ON TOP of a070b639a).

**Ref topology (important):** intcell @6efdfface = corankrec @a070b639a + the atom. corankrec is
**NOT** an ancestor of genm-integration. Integration's `RouteMSJCorankRec.lean` is 98 lines SHORTER
than corankrec's — it is **missing the entire interior-QIP family** (see (a)/§merge-debt below). The
mountain files (HcellNull, ChargeFactor, InteriorShell, InteriorLoss, CorankSlabD, FrontChargeBox,
DecoratedRec) exist only on integration, NOT on intcell/corankrec. The atom (RadialCriticalPower,
RadialResidualPower's critical sibling) exists only on intcell, NOT on integration.

---

## Headline (what to reuse / avoid / what's staged)

The interior per-cell terminal `∫_cell frontChargeIntegrand < ⊤` is **fully scaffolded, sorry-free,
down to one isolated analytic hole** — the COUPLED boundary-RLCT estimate
`∫_{z,A_cor} charge(p)·frontLossIntegral(p) < ⊤` (couplerad ★5 / `coupled_hfin_cell`). Everything
above it composes: `coupledCell_interior_lt_top` (FrontChargeBox) reduces the coupled cell to
`hfront = ∫_cell frontChargeIntegrand` (+ hGae + hEtopae + hc'); `frontCharge_cell_lt_top_of_freebox`
(corankrec) reduces `hfront` to the box-level free-box; `frontChargeBox_lt_top_of_hfin` (FrontChargeBox)
glues per-cell to box via the atlas cover. **CONSUME** these — do not rebuild them. The **charge/loss
factoring bridge** the HcellNull docstring flags as "not yet landed" IS landed:
`frontChargeIntegrand_eq_charge_mul_loss` (ChargeFactor) — that docstring line is STALE. **AVOID** the
"square-first freebie" (interior gate reduces to `chargeFreeBox_lt_top` via a bounded/factored-out loss)
— corankrec/couplerad refuted it (LATE-27 calibration correction): the loss is per-`p` finite but NOT
uniformly bounded, so the charge free-box alone does NOT close the cell; it is only the CHARGE LEG inside
the coupled integral. **STAGED for exactly this build:** the atom (`radial_morse_critical_power_le` + its
supercritical sibling), the full QIP family (`minAdm_le_inf_pivot_qip` et al.), the interior-loss
box-RLCT brick (`interiorLoss_twoMat_lt_top`), the charge free-box (`chargeFreeBox_lt_top` consuming
slabD), and the b-split wrapper (`routeMBoxThresholdFinite_of_coupled_bsplit`).

**ROUTE STATUS (LATE-84/85 Q2-gate flip — NEWER than the LATE-51 committed priorities.md):** the mint
FLIPPED to the DECORATED capstone (`routeMBoxThresholdFinite_of_decoratedDescent`). The coupled b-split
(`routeMBoxThresholdFinite_of_coupled_bsplit`) is now a **u≤2 PARTIAL** — Q2-clean only for
`u = min(M₀,M₁) ≤ 2` saturated waists; it INHERITS the Q2 obstruction for u≥3, and every ∀-M chain with
min(M₀,M₁)≥3 hits a u≥3 waist. **BUT the interior CONTENT is route-agnostic** (see (d)): the interior
per-cell finiteness + its bricks are Q2-CLEAN and REUSABLE by the decorated step's easy cells. Only the
u≤2 saturated-waist WRAPPER is the partial dead-end.

---

## (a) CONSUME — banked, sorry-free, reuse it

### The atom (LANDED, unified isotropic leaf) — owner **intub** (`tide/genm-intcell` @6efdfface)
`lean/DLNFibre/DLN/RLCT/Validate/RadialCriticalPower.lean` (sorry-free, S2-FREE, only analytic input
`euclidND_ball_integrable`):
- `critBallConst (m : ℕ) (s R : ℝ) : ℝ` (:34) — the `P`-independent ball constant `∫_{ball_R⊆ℝ^{m+1}} ‖P‖^{−s}`.
- `lintegral_ball_critical_le` (:48) — ball form, `2q ≤ ub` (regimes ①②, incl. the log boundary `c'=(m+1)/2`
  folded to `w^{−ε}` for arbitrary small ε).
- `radial_morse_critical_power_le` (:92) — the box form, drop-in sibling of the supercritical
  `radial_morse_residual_power_le` (RadialResidualPower, `2q>ub` regime ③, banked on BOTH refs).
- **Confirmed the unified isotropic leaf:** the "clean-three" = supercritical (`radial_morse_residual_power_le`)
  + critical/subcritical (`lintegral_ball_critical_le`/`radial_morse_critical_power_le`) cover all of
  couplerad §w3-boundary regimes ①②③ via the ε-window; ε nonempty iff `2c' < ub + minAdm(![u+a,u,d])`
  (the QIP `minAdm_le_inf_pivot_qip`). S2-free, no `monomial_rlct`.

### corankrec scaffolding + QIP — owner **corankrec** (`genm-corankrec` @a070b639a)
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorankRec.lean` (sorry-free, NATIVE):
- `BindingShell M t j` (:43) — the binding-shell scope predicate (htb + hbind + interior).
- `hGae_cell_interior` (:70) — the corank-Gram `Q_bQ_bᵀ` PosDef a.e. ON an interior cell (the `hGae`
  slot of `coupledCell_interior_lt_top`). NATIVE = box-level `hGae_from_deepRank` restricted via `ae_mono`.
- `frontCharge_cell_lt_top_of_freebox` (:93) — reduces the CELL front-charge `hfront` to a box-level
  `hfreebox` hypothesis via `lintegral_mono_set` (cell ⊆ box). **This is the box→cell reduction.**
- `cellRank_le_deepTailMin` (:112) — the trichotomy cap (feeds the null-layer discharge).
- **QIP family (integration is MISSING these — corankrec-only):** `bindingCut_ab_le_deepTailMin_succ`
  (:129, the deep-corank-empty scan: a+b ≤ deepTailMin+1, no b≥2 regime — powers HcellNull's 4-way cover),
  `minAdm_le_head_mul_min_deepTailMin` (:159), `minAdm_le_interior_qip` (:178, `≤ u·M₂+(M₁−u)·M₀`),
  `minAdm_le_interior_qip_deepTailMin` (:200), `minAdm_le_u_deepTailMin_add_peelCharge` (:223, form A,
  tightest), `minAdm_le_inf_pivot_qip` (:239, **couplerad's cited pivot-independent object**).

### The interior terminal + atlas glue — owner **arch1build** (`genm-integration`)
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJFrontChargeBox.lean` (sorry-free):
- `projDeep` (:28), `deepFactor_rank_le_rows` (:35) — the cover-completeness helper.
- `frontChargeBox_lt_top_of_hfin` (:46) — **cell→box glue**: box `∫ frontChargeIntegrand < ⊤` from per-cell
  `hfin`, via the deep-rank atlas cover (`deepRankLE_eq_iUnion_cells`) + `lintegral_lt_top_of_finite_cover`.
- `coupledBox_lt_top_of_cells` (:86) — the same glue for `coupledBoxIntegrand`.
- `coupledCell_le_frontCell` (:123) — coupledBox ≤ frontCharge on a cell (per-`p` step-2 under
  `lintegral_mono_ae`, needs hGae+hEtopae+hc').
- `coupledCell_interior_lt_top` (:148) — **THE interior terminal**: `∫_cell coupledBoxIntegrand < ⊤`
  from (hc': `ab/2 < c'`) + (hGae) + (hEtopae) + (**hfront**: `∫_cell frontChargeIntegrand < ⊤`).
  The interior arm reduces EXACTLY to `hfront`.

### The charge/loss factoring bridge — owner **deephier/couplerad design → arch1build** (`genm-integration`)
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJChargeFactor.lean` (sorry-free):
- `frontLossIntegral` (:41) — the pure loss `∫_x (E_top+E_tr)^{−q}` with the x-independent charge stripped.
- `chargeGram_det_nonneg` (:61).
- `frontChargeIntegrand_eq_charge_mul_loss` (:78) — **THE bridge**: `frontChargeIntegrand = ofReal(charge)·frontLossIntegral`,
  `charge = det(Q_bQ_bᵀ)^{−a/2}·Cresid`. **This IS the "frontChargeIntegrand ↔ chargeGramDet bridge"
  the HcellNull docstring calls "not yet landed" — that docstring is STALE (see (c)).**

### The per-`p` loss brick — owner **intloss** (`genm-integration`)
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJInteriorLoss.lean` (sorry-free):
- `finrank_range_matMulRight` (:103) — crux rank identity `finrank(range(X↦X·A)) = r·rank A` (Mathlib
  v4.29 lacks `rank_kronecker`; genuinely new).
- `interiorLoss_twoMat_lt_top` (:172) — the per-`p` loss box-RLCT: `∫_box (frobSq(W·S)+frobSq(C·K))^{−q} < ⊤`
  iff `2q < rW·rank S + rC·rank K`. The LOSS leg at fixed `p` (fixed S,K = the Q̃ₚ factors).

### The charge free-box + slabD inner slab — owners **intmtn/schurB** + **slabD** (`genm-integration`)
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJInteriorShell.lean` (sorry-free):
- `chargeFreeBox_of_inner` (:227) — outer `A_cor`-integral closes given the `b`-general inner uniform bound.
- `chargeFreeBox_lt_top` (:256) — **the FULL interior CHARGE free-box, unconditional, general a,b**:
  `∫∫_{(A_cor,S)∈box} det((A_cor·S)(A_cor·S)ᵀ)^{−a/2} < ⊤` for `a+b ≤ min(n,p)`. Consumes slabD.
- log-integrability atom (re-homed as EDGE tool): `log_one_div_le_rpow_neg` (:45),
  `shellLogWeight_integrableOn` (:68), `shellLogWeight_lintegral_lt_top` (:115).

`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCorankSlabD.lean` (sorry-free) — owner **slabD**:
- `corankSlabD_charge_sint_le` (:560) — **the (D) b≥2 inner charge slab**: `∃C<⊤, ∀A_cor,
  ∫_S chargeGramDet^{−a/2} ≤ C·det(A_cor A_corᵀ)^{−a/2}` for `b≤n ∧ a+b≤p`. Plus the CoV kit
  (`measurePreserving_colMulLeft`:127, `exists_canonical`:374, `bRowGram_colBall_lt_top`:159,
  `activeGram_colBall_lt_top`:477).

### The b-split dispatch wrapper — owner **intmtn** (`genm-integration`)
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJHcellNull.lean` (sorry-free):
- `coupledBox_cell_lt_top_of_generic` (:38) — the null-layer discharge (deficient cells `∫=0`,
  reduces `∀i` to the generic cell). Integrand-agnostic, unconditional.
- `GenericCellFinite M u c'` (:101) — the per-generic-cell Prop.
- `coupledBox_cell_generic_of_bsplit` (:124) — the 4-way dispatch (interior/edge × b=1/b≥2), cover by
  `bindingCut_ab_le_deepTailMin_succ`.
- `routeMBoxThresholdFinite_of_coupled_generic` (:66), `..._of_coupled_bsplit` (:189) — the per-`M`
  closure (now a u≤2 partial; see (d)).

---

## (b) OPEN — the remaining composition sub-steps + rough size

Everything reduces to ONE analytic mountain: the interior per-generic-cell terminal
`∫_cell frontChargeIntegrand < ⊤` at the RRR-floor (equivalently, via corankrec, the box-level free-box
`∫_box frontChargeIntegrand < ⊤`, which after the factoring bridge is the COUPLED integral
`∫_{z,A_cor} charge(p)·frontLossIntegral(p) < ⊤`). Design = couplerad-cert.md ★1–★5 + §2.

Sub-step banked/open status (the task's named chain):
1. **R1 (Frobenius/per-cell split)** — BANKED. The atlas cover `deepCover_aux` + `frontChargeBox_lt_top_of_hfin`
   (cell→box) + `frontCharge_cell_lt_top_of_freebox` (box→cell) + null-layer discharge. No new work.
2. **The charge/loss factoring (Φ separation)** — BANKED: `frontChargeIntegrand_eq_charge_mul_loss`.
3. **The per-`p` LOSS box-RLCT** — BANKED brick: `interiorLoss_twoMat_lt_top` (finite iff `2q < rank-sum`).
   Gives `frontLossIntegral(p) < ⊤` per-`p`; NOT the coupled integral.
4. **The CHARGE free-box (det-monotone PSD Gram, δ=0)** — BANKED: `chargeFreeBox_lt_top` (+ slabD). The
   charge leg, uniform in the loss variables.
5. **R2 (deep z0↦Y CoV) + per-row-(Q_bQ_bᵀ)^{1/2} CoV + Tonelli → the COUPLED estimate** — **OPEN. THE MOUNTAIN.**
   This is couplerad ★5: after the front fibre-peel + residual-power peel, the binding (deepest) cell is the
   NON-SQUARE bilinear corank recursion `frobSq(Front·Z_deep)^{−q'}·det(Q_bQ_bᵀ)^{−a/2}` = the arity-3
   RRR-with-charge for the sub-chain `(u,M₂,n)`, floor `minAdm(u,M₂,n)`, reached with NO slack.
   - **Square case** (`u=M₂=n`, e.g. (4,4,4,4)): reachable by the banked square `SchurCore` /
     `routeMBoxThresholdFinite_rrp` (RouteMBoxThresholdRRP). ~plumbing (Fubini + raw-pi CoV [Matrix.module
     diamond] + A/B atom composition + charge-domination). Rough size: multi-lemma, ~medium.
   - **Non-square case** (`exc>0` or `u≠M₂`, e.g. (3,4,5,4)→reduced (2,5,4)): NEITHER the exponent-preserving
     fibre-peel NOR the square SchurCore reaches the floor (factor-of-2 undershoot, same as the (3,3,3,3)
     wall). Needs the **general non-square bilinear corank recursion** (rank-stratified {V=0}). Rough size:
     the load-bearing new build, "more than one lemma", split into corankrec (square plumbing) + schurrec
     (`SchurRecStep`, rectangular Δ, SVD-free via banked hGae + ★4). This is `coupled_hfin_cell:82` — the
     documented single sorry on the corankrec interface.

The 4 b-arms of `routeMBoxThresholdFinite_of_coupled_bsplit` (HcellNull) are the honest holes:
`h_int_b1` (charge-factoring + coupled est., `chargeFreeBox_b1a1` leg), `h_int_b2` (coupled est. +
slabD via `chargeFreeBox_of_inner`), `h_edge_b1` (edgered corank-one brick), `h_edge_b2` (R2, couplerad).
Interior arms h_int_b1/b2 each = `coupledCell_interior_lt_top` fed by the mountain's per-cell output.

---

## (c) CONTRADICTIONS / STALE flags (verify live, don't trust the log)

1. **STALE:** `RouteMSJHcellNull.lean` docstrings (:26, :62) say the interior arm goes "through a
   `frontChargeIntegrand ↔ chargeGramDet` bridge NOT yet landed." **That bridge IS landed** as
   `frontChargeIntegrand_eq_charge_mul_loss` (ChargeFactor:78, sorry-free on the same branch). Don't
   re-derive it.
2. **REFUTED / DEAD (do not build):** `RouteMSJInteriorShell.lean`'s head docstring (arch1build's read)
   claims "the loss factor is x-independent and BOUNDED on the interior generic cell ... so it pulls out
   and the gate reduces to the charge" — the **"square-first freebie."** This is an OVERCLAIM (git log
   LATE-27 "CALIBRATION CORRECTION": corankrec caught, couplerad fixed cert). `RouteMSJChargeFactor.lean`'s
   docstring (:20, intloss's numerical witness) is the CORRECTED view: `frontLossIntegral p` is per-`p`
   finite but blows up `~σ_min(L_p)^{−2q}→∞` as `p→` loss-degeneracy locus — NOT uniformly bounded, so no
   `p`-independent `D`, so the factored `[bound]·[chargeFreeBox]` route is DEAD. The interior is the
   COUPLED integral. **`chargeFreeBox_lt_top` is the CHARGE LEG, not the interior closer.** (Note: LATE-51
   priorities.md still headlines "LOSS-COUPLING RESOLVED = CHARGE-ONLY" — that optimism was itself
   superseded by the LATE-84/85 flip; treat "charge-only" as the dead freebie.)

---

## (d) ROUTE-AGNOSTIC vs COUPLED-SPECIFIC split (the LATE-84/85 flip)

**Source:** discuss-at-close #3176–3181 (LATE-85), endgame-lanes.md LATE-84/85/§square-scoping.
q2gate verdict (5 decorrelated confirmations): the plain reduced-chain IH cannot carry the FaithfulSJAt
`H⁻⁴` weight ("Q2"). Coupled is Q2-CLEAN only for `u = min(M₀,M₁) ≤ 2`; it INHERITS Q2 for u≥3. The
∀-M mint hits a u≥3 waist on every chain with min(M₀,M₁)≥3 ⟹ the mint routes through the DECORATED
capstone (`routeMBoxThresholdFinite_of_decoratedDescent`, RouteMSJDecoratedRec:216). Decision A (bypass
decorated) is REVERSED.

**ROUTE-AGNOSTIC (transfers to decorated — same finiteness content, different wrapper):**
- The interior per-cell terminal `coupledCell_interior_lt_top` + `frontCharge_cell_lt_top_of_freebox`
  + the coupled boundary-RLCT estimate (the mountain, ★5). Q2-CLEAN (native RectSchurCore). REUSABLE by
  the decorated step's "easy cells."
- The atom, the QIP family, `interiorLoss_twoMat_lt_top`, `chargeFreeBox_lt_top` + slabD, the
  factoring bridge, the atlas cover/null-discharge. All route-agnostic BRICKS.
- The EDGE arm (`GenericCellFinite` / coupled descent) is likewise reusable.

**COUPLED-SPECIFIC (u≤2 partial dead-end for ∀-M):**
- `routeMBoxThresholdFinite_of_coupled_bsplit` / `..._of_coupled_generic` (HcellNull) — the per-`M`
  single-binding-cut WRAPPER. Q2-clean only at u≤2 saturated waists; the plain SJStepHyp →
  `routeMBoxThresholdFinite_of_step` capstone CANNOT discharge the u≥3 waists. This wrapper "becomes a
  u≤2 partial" (endgame-lanes:600). Not wrong, not wasted — but NOT the ∀-M closer.

**DECORATED interface (how the interior content feeds it):**
`RouteMSJDecoratedRec.lean` — the live driver is `routeMBoxThresholdFinite_of_decoratedDescent` (:216)
← `DecoratedDescent` (:206) = `∃ adm, (trivial admissible) ∧ DecoratedStepHyp adm ∧ DecoratedBaseHyp adm`.
- `DecoratedStepHyp adm` (:144) — the DECORATED step: for a ≥3-width chain, given the DECORATED strong IH
  (box-finiteness for every adm-admissible decoration of every one-shorter chain), every adm-admissible
  decoration of M is finite below carrier threshold. The IH carries `H⁻⁴` inside the `SJDecoration`.
- `DecoratedBaseHyp adm` (:154), `decoratedBoxThresholdFinite_of_decoratedStep` (:161, mechanical arity
  strong-induction), `routeMBoxThresholdFinite_of_decoratedStep` (:190).
- **DEAD:** the plain-IH `DecoratedPeelStep` (:78) + `routeMBoxThresholdFinite_of_decoratedPeel` (:99) —
  its antecedent `∀M', RouteMBoxThresholdFinite M'` (PLAIN undecorated IH) is UNPROVABLE (Q2). Do not
  target it.
- **Interior content is route-agnostic:** the interior per-cell finiteness is the SAME analytic fact in
  both routes; in decorated it discharges the EASY (non-square-u≥3) cells of `DecoratedStepHyp`, with the
  `H⁻⁴` Gram weight riding in `adm`'s carrier/jac (the coupled route's `det(Q_bQ_bᵀ)^{−a/2}` charge is
  the same Gram weight). The genuinely coupled-specific, decorated-only crux is the **square u≥3 waist**
  (a=b=0, corank-2 γ=1, ρ∉L⁴) — narrowed per endgame-lanes §square-scoping; tall/wide non-square u≥3 may
  be native (satred's qbox). decstep adjudicates `DecoratedStepHyp` provable-or-wall.

---

## Proposed ownership boundary (avoid collision)

- **intub** — owns the atom (RadialCriticalPower, `tide/genm-intcell`). DONE. No further build; CONSUME.
- **corankrec** — owns the QIP family + the 3 arch1build slots (hGae_cell_interior, frontCharge_cell_lt_top_of_freebox,
  cellRank) + `coupled_hfin_cell` interface + the SQUARE half of the mountain plumbing (couplerad ★5 square).
  **MERGE-DEBT: the QIP family is NOT on genm-integration** — must be merged before any consumer builds.
- **schurrec** — owns the NON-SQUARE half (`SchurRecStep`, rectangular Δ, the load-bearing new build).
- **intmtn** — owns the b-split wrapper (HcellNull) + InteriorShell assembly. The wrapper is now a u≤2
  partial; keep it banked. Do NOT extend it to u≥3.
- **intloss** — owns `interiorLoss_twoMat_lt_top` (the loss leg). DONE; CONSUME.
- **slabD** — owns `corankSlabD_charge_sint_le` (the b≥2 inner charge slab). DONE; CONSUME.
- **schurB** — owns the charge free-box family in InteriorShell (`chargeFreeBox_*`). DONE; CONSUME as the
  charge leg (NOT the interior closer).
- **arch1build** — owns FrontChargeBox (terminal + atlas glue) + ChargeFactor (bridge). DONE; CONSUME.
- **The COMPOSITION** (the mountain ★5, the coupled estimate) — commission to corankrec (square) +
  schurrec (non-square), feeding `coupled_hfin_cell` → `coupledCell_interior_lt_top` → the interior arms.
  For the ∀-M mint, wire the interior output into the DECORATED step (decstep), NOT the coupled b-split.

**Do NOT rebuild** (already built, twice-rebuilt risk): the factoring bridge (ChargeFactor:78), the
charge free-box (InteriorShell:256 + slabD:560), the interior loss brick (InteriorLoss:172), the atlas
cover glue (FrontChargeBox:46/86), the null-layer discharge (HcellNull:38), the QIP family
(CorankRec:129–239, but MERGE it to integration first).

**Dead/superseded routes to AVOID:** the square-first freebie (charge-only interior); plain-IH
`DecoratedPeelStep`; Route-A frontCharge-a.e.-over-box (diverges at edge, LATE-50); the whole Route-B
deep-atlas Arch-2 arc (off mint path, LATE-15); the exponent-preserving iterated-fibre peel for
non-square cuts (factor-of-2 undershoot).
