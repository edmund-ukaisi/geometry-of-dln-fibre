# Statement card — Step Ψ_conj (LINK-1) reduction skeleton + assembled bridge (#120 `hstep2`)

Thread `genm-hstep2psiconj`, off `origin/genm-hstep2close2` (@203bccac, which carries the LANDED
unconditional general-`L` Step Θ `link2_at_wstar_gaugeReg_gen` + `Kcoup_zero`). Closing the #120
`hstep2` via `hstep2 = Step Θ ∘ Step Ψ_conj`. This card covers the **LINK-1 analytic reduction
skeleton** + the **assembled compose** (pieces 2-plumbing + 3), and reports the remaining coupled bulk.

Branch `origin/genm-hstep2psiconj` @ `490887df`.
Lean module: `lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeGenConj.lean` (new, ~200 LoC, sorry-free).

## What lands here (sorry-free, clean-three)

> **Claim (LINK-1, the general-`L` conjugate diffeo bridge — analytic reduction).** For `1 ≤ L`, given an
> abstract flat local diffeo `psi` at `wstar` (`ContDiff ⊤`, strict derivative the identity, fixing
> `wstar`), its split-side action `psiSplitRaw` (`split ∘ psi =ᶠ[𝓝 wstar] psiSplitRaw ∘ split`), and the
> two coupled germs
> - **`hsub3reg`** (reg preservation): `∑ (regStraighten (psiSplitRaw (split x))).1² = ∑ (regStraighten (split x)).1²`;
> - **`hsub4core`** (core untwisting): `coreF(deepestCoreAbsorbConj (psiSplitRaw (split x))).2.1 = Score x`,
>
> the RLCT of `Φscore = ∑ (regStraighten (split x))².1 + Score` at `wstar` equals the RLCT of the
> **conjugate** absorbed-core energy `∑ (regStraighten (split x))².1 + coreF(deepestCoreAbsorbConj (split x)).2.1`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepest_diffeo_bridge_gen_conj_impl`.
> - **Proof.** The three germs give `Φcore_conj ∘ psi =ᶠ[𝓝 wstar] Φscore`; `rlctAtOn_diffeo_bridge_of`
>   (banked) strips the diffeo. Mirrors the L=2 `deepest_diffeo_bridge_L2_conj_impl`, abstracting over the
>   concrete `psiL2Conj` / `psiSplitRawL2CoreConj`.

> **Claim (assembled — the BARE canonical target `hstep2` consumes).** For `2 ≤ L`, composing LINK-1 with
> the LANDED general Step Θ (`link2_at_wstar_gaugeReg_gen`) gives
> `rlctAtOn Φscore wstar = rlctAtOn (∑ (regStraighten (split x))².1 + coreF(deepestCoreAbsorb (split x)).2.1) wstar`
> — exactly the RHS of the `hstep2` sorry at `DeepestL2Wiring:1060` (L ≥ 3 arm).
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepest_diffeo_bridge_gen_assembled`.
> - **Proof.** `rw [deepest_diffeo_bridge_gen_conj_impl …]; exact link2_at_wstar_gaugeReg_gen …`. Mirrors
>   `deepest_diffeo_bridge_L2_assembled`. Θ's frame data (`J = frontEmbed`, per-layer `hPtri`/`hQtri`,
>   `hbdy`, endpoint units) enter as hypotheses (all wire-dischargeable).

- **Proved.** Both theorems sorry-free at general `L`, axiom footprint `[propext, Classical.choice, Quot.sound]`
  (clean-three, forced `#print axioms`, no `sorryAx`).
- **Assumed (explicit hypotheses — the coupled bulk, NOT laundering).** The concrete `psi`/`psiSplitRaw`
  (the general Ψ_conj) + the diffeo triple + the split-compat germ + `hsub3reg`/`hsub4core`. These isolate
  the RLCT/diffeo plumbing from the genuinely hard construction; Codex (xhigh) vetted this as a faithful
  reduction. The analogous NAIVE reduction `deepest_diffeo_bridge_gen_impl` (already banked) has the same shape.
- **Cited.** none new. Reuses banked `rlctAtOn_diffeo_bridge_of` + the LANDED unconditional general Step Θ
  `link2_at_wstar_gaugeReg_gen`.
- **Status.** sorry-free (pending fidelity review).

## Key finding (steers the remaining work): the general Ψ_conj is a JOINT move, not a pure conjugation

A pure core-shear conjugation `psi = split⁻¹ ∘ deepestCoreAbsorbConj⁻¹ ∘ (deepestPsiCoreShear K) ∘
deepestCoreAbsorbConj ∘ split` (whose fderiv at `wstar` IS the identity — the conjugation cancels the
nonzero shift-derivative, `coreShearSymmCLM Dδ ∘ coreShearCLM Dδ = id`) touches ONLY the core slot. But
`deepestEFull` reads the core slot (via `framedParamsPivot` → the full framed product `∏C`), so a pure
core edit changes `deepestEFull` and BREAKS `hsub3reg` (reg preservation). Verified against the def
(`DeepestGaugeConstruction:419`) + Codex xhigh (0.9). The general Ψ_conj MUST be the L=2 **joint move**:
a core shear plus a canonical reg/gauge fibre correction that keeps `deepestEFull` exactly invariant while
the core edit realises the Schur untwisting to `Score` (the honest chain). This is why the L=2
`psiSplitRawL2CoreConj` edits both the last-layer core `T1 ↦ T1'` AND the reg/gauge `Y1 ↦ Y1'` jointly.

## Remaining to CLOSE `hstep2` (precise — the coupled bulk, a separate tide)

The `hstep2` sorry is LEFT UNTOUCHED (not laundered). To close it, instantiate `deepest_diffeo_bridge_gen_assembled`
at `DeepestL2Wiring:1060` and discharge (Θ's frame data is already in scope there from the triangular bundle):

1. **The concrete general Ψ_conj `psi`/`psiSplitRaw` + diffeo triple + split-compat.** The joint move:
   core shear (per-layer `S_s ↦ (1−K_s)·S_s`, `K = Kcoup(Ĉ)` the honest-chain coupling) + the canonical
   reg/gauge correction preserving `deepestEFull` (general lift of L=2's `l2g'Conj`/`l2Y1'`). ContDiff /
   strict-fderiv-id-at-`wstar` / fixpoint mirror `psiL2Conj_*` (via a cutoff `χ`). Comparable to the L=2
   `DeepestDiffeoBridgeL2Conj.lean` machinery (~2700 lines).
2. **`hsub4core` (core = Score).** Consumes banked `deepestCoreF_coreAbsorbConj_eq_prodSchur` (reduces the
   conj absorbed core to `‖∏_s (decode(core)_s + Δ_s)‖²`) → the honest chain identity
   `blockSchur(partProd Ĉ L) = ScoreSchur` (numerically certified, NOT yet in Lean: needs the `Fin L ↔ ℕ`
   cast resolution of `Ĉ` + `partProd Ĉ L = reindex(prod decode)` + the frame-strip/corner to framed
   `Score` via `schur_frame_transform` + `rcore_eq_schur_of_corner_split`), via `schur_product_ldu_rec` +
   `Kcoup_zero`.
3. **`hsub3reg` (reg preservation).** The general reg-invariance of the joint move — the general lift of
   `hsub3reg_conj_germ` (L=2, `DeepestL2ConjReg`), whose L=2 proof is the residual-block algebra
   `resid_regBlocks_eq_of_mid_agree` / `conj_hm_triple` / `deepestEFull_sq_sum_of_resid_blocks`.

## Build status
- Isolated green: `scripts/lb DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeGenConj` ✓ (2749 jobs).
  Forced `#print axioms` clean-three (both theorems). `rg`: no name clashes with siblings (new top-level
  names `deepest_diffeo_bridge_gen_conj_impl` / `deepest_diffeo_bridge_gen_assembled` are unique).
- Aggregator wiring (`DLNFibre.lean`, AxCheck) is the CONTROLLER's (single-writer); the module is
  integration-ready.
