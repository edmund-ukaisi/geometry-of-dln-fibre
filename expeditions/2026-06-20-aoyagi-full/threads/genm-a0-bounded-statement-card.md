# Statement card — `frontCollapse_wide_bounded_lt_top` (Lane 1 §1, the a=0 wide bounded arm)

**Claim.** The a=0 wide BOUNDED arm of the front-collapse atom: for a wide architecture
(`M₀≤M₁`) in the bounded density regime (`M₂<M₁−M₀+1`), the front-collapse box integral is finite
below `½·minAdm`, given the plain one-shorter IH.

- **Lean.** `DLNFibre.DLN.RLCT.frontCollapse_wide_bounded_lt_top`
  (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJFrontCollapseWide.lean`, on `origin/genm-lane1-shell`
  @`3dde58549`; 415 LoC):

      theorem frontCollapse_wide_bounded_lt_top {L : ℕ} (M : Fin (L+1+1+1) → ℕ)
          (hwide : M 0 ≤ M 1) (hbnd : (M 2 : ℝ) < (M 1 : ℝ) - M 0 + 1)
          (hIH : ∀ M' : Fin (L+1+1) → ℕ, RouteMBoxThresholdFinite M')
          (c' : NNReal) (hc' : (c':ℝ) < (minAdm M : ℝ) / 2) :
          (∫⁻ F in wingFrontBox M, ∫⁻ A' in paramsBoxM (tailChain M) 1,
              ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c':ℝ)))) < ⊤

- **Gloss.** Over the full-row-rank front box (`wingFrontBox` = leading-block invertible), collapse the
  front factor `F`: the fixed-F CoV absorbs `F` into a free-Wishart Gram Jacobian, the residual reduces
  to the one-shorter reduced chain (finite by the plain IH), and the density stays integrable because the
  bounded regime `M₂<M₁−M₀+1` keeps the front-Gram qbox exponent subcritical.

- **Proved.** Sorry-free. 8-step route (lane1shell's derivation, a0wire's build):
  (1) `det(F·Fᵀ)≠0` from `wingFrontBox` (rows lin-indep → Gram PosDef → det≠0) — **CLOSED internally**,
  no residual hypothesis; (2)/(3) chain front-peel + Tonelli via the generic `frontFactor_split`
  (closes the L=0/L≥1 dependent-length split); (4)/(8) pointwise-in-F fixedF bound
  (`fixedF_wide_cov_bound`) + `setLIntegral_mono` over F + product-of-finites; (5)/(6) `∫_{W box M₁} g < ⊤`
  via front-split of `redChain` (finite by `redChain_box_lt_top`) + W-radius scaling
  (`lintegral_comp_rmatMulLeft` with `G=M₁·I` + `frobSq_rmatMul_smul` homogeneity; degenerate
  `M₁=0 ⟹ M₀=0` branch handled separately); (7) `front_gram_qbox_lt_top`.

- **Reusable infra (added in-file, flagged for Core-lift on 2nd use):**
  `eFrontN`/`measurePreserving_eFrontN`/`eFrontN_preimage_box`, `frontFactor_split` (generic pre-factored
  front-split), `rmatMul_mul_assoc`, `rmatMul_one_left`, `volume_matBox_lt_top`.

- **Assumed.** wide `M₀≤M₁`; BOUNDED regime `M₂<M₁−M₀+1`; `c'<½·minAdm M`; the plain one-shorter IH
  `∀ M', RouteMBoxThresholdFinite M'` (an IH, NOT a cite or a strengthening — the LATE-102 false-decoupling
  check passes).

- **Cited.** none. Consumes banked bricks: `fixedF_wide_cov_bound`/`lintegral_comp_rmatMulLeft` (fcov),
  `exists_ortho_complement_rows` (rowcomp), `wingFrontBox`/`front_gram_qbox_lt_top`/`redChain_box_lt_top`
  (lane1shell RouteMSJFrontCollapse), `prod_front_peel` (RouteMFrontPeel), `frobSq_rmatMul_smul`
  (RouteMSJCornerLoss).

- **Deferred.** BOUNDED regime only. The LOG (`M₂=M₁−M₀+1`, δ-fold) + POWER (`M₂≥M₁−M₀+2`, the (r,s) atlas)
  regimes of the a=0 wide arm, the b=0 tall wing, and the d=1 arms (§2) are separate builds.

- **Status.** sorry-free; forced `#print axioms` clean-three `[propext, Classical.choice, Quot.sound]`;
  full closure green (8337 jobs, no name clash). **a0rev** decorrelated fidelity review IN FLIGHT
  (fidelity + `frontFactor_split` soundness + clean-three). Pinned SHA @`3dde58549`.
