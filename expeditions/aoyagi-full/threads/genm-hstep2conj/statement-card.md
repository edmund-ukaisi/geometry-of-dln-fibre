# Statement card — #120 `hstep2` piece 5c: the general-`L` conjugate diffeo bridge

> **Claim.** The general-`L` (L ≥ 3) `hstep2` RLCT equality `rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`
> reduces — via the **conjugate flat diffeo** `Psi = split⁻¹ ∘ coreAbsorb⁻¹ ∘ Ψ ∘ coreAbsorb ∘ split`
> (`Ψ = deepestPsiCoreShear K` the banked absorbing shear) — to **two geometric germ hypotheses**: the
> Schur untwisting `huntwist` and the reg-preservation `hreginv`. The reduction, and the
> chain-independent analytic diffeo triple it stands on, are proved sorry-free from banked pieces.
>
> - **Lean (`lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeGen.lean`, branch `genm-hstep2conj`):**
>   - `hasStrictFDerivAt_coreShearHomeo_zero` — the forward mirror of the banked
>     `hasStrictFDerivAt_coreShearHomeo_symm_zero` (`D(coreShearHomeo shift)(0) = id` when `D(shift)(0) = 0`).
>   - `deepestGConjFlat` — the conjugate flat diffeo `split⁻¹ ∘ coreAbsorb⁻¹ ∘ Ψ ∘ coreAbsorb ∘ split`.
>   - `contDiff_deepestGConjFlat` (ContDiff ⊤, given `hKcd`), `hasStrictFDerivAt_deepestGConjFlat`
>     (`dPsi(wstar) = id`, given `hKcd`+`hK0`+`split wstar = 0`), `deepestGConjFlat_fixpoint`.
>   - `deepest_diffeo_bridge_gen_impl` — the reduction of `hstep2` to `huntwist` + `hreginv`.
> - **Gloss.** `coreAbsorb = deepestCoreAbsorb` turns the raw core `T_s` into the per-layer Schur core
>   `S_s = T_s − Z_s(1+X_s)⁻¹Y_s`, so `deepestCoreF (coreAbsorb q).2.1 = ‖∏ S_s‖²`. `Ψ` shears the
>   already-Schur core, `S_s ↦ (1−K_s)S_s`, so `deepestCoreF (Ψ (coreAbsorb q)).2.1 = ‖∏(1−K_s)S_s‖²`.
>   The CONJUGATE `Psi` (with the outer `coreAbsorb⁻¹`) lets `Φcore ∘ Psi` read `deepestCoreF (Ψ
>   (coreAbsorb (split x))).2.1` on the core (= `Score x` by `huntwist`) and `regStraighten` on the
>   reg/spec (invariant by `hreginv`, since `Psi` fixes reg+spec of `split x`), i.e.
>   `Φcore ∘ Psi =ᶠ[𝓝 wstar] Φscore`. `Psi` is a local diffeo at `wstar` (`dPsi(wstar) = id` via
>   `deepestSplitCLE⁻¹ ∘ id∘id∘id ∘ deepestSplitCLE`), so `rlctAtOn_diffeo_bridge_of` closes.
> - **Proved.** All five statements, unconditionally on `L`/`H`/`r`, given the named hypotheses. Route:
>   the diffeo triple is assembled from the banked smoothness of `split^±` (`contDiff_deepestSplit(_symm)`,
>   `hasStrictFDerivAt_deepestSplit(_symm)`, `deepestSplitCLE`), `coreAbsorb^±`
>   (`contDiff_coreShearHomeo(_symm)`, `hasStrictFDerivAt_coreShearHomeo_symm_zero`, this file's forward
>   `_zero`, `contDiff_schurCutoffShift`, `hasStrictFDerivAt_schurCutoffShift_zero`), and `Ψ`
>   (`contDiff_deepestPsiCoreShear`, `deepestPsiCoreShear_isLocalDiffeoAt`). The reduction combines the two
>   germs by `filter_upwards` + the `split⁻¹∘split` / `coreAbsorb∘coreAbsorb⁻¹` cancels, then
>   `rlctAtOn_diffeo_bridge_of`.
> - **Assumed (the two germs — the DEFERRED coupled geometric BULK, pieces 4 + 5a/5b, NOT closed here):**
>   - `hKcd : ∀ s, ContDiff ⊤ (K s ·)`, `hK0 : ∀ s, K s 0 = 0` — the coupling `K`'s analytic data
>     (**piece 4**, the concrete DLN coupling `K = Kcoup (Cq q) s`);
>   - `huntwist` (germ): `deepestCoreF (Ψ (coreAbsorb (split x))).2.1 = Score x` (**piece 5a**, the
>     `schur_product_ldu_rec` untwisting + the `Fin (H k)` cast + `rcore_eq_schur_of_corner_split` +
>     `schur_frame_transform`);
>   - `hreginv` (germ): `(regStraighten (coreAbsorb⁻¹ (Ψ (coreAbsorb (split x))))).1 = (regStraighten
>     (split x)).1` (**piece 5b**, the general-`L` E2 reg-preservation — `deepestEFull` reads the core
>     slot at the last layer, so this is NOT automatic; analog of L=2's `e2_regPreserve`/`hsub3reg`).
> - **Cited.** None. Forced `#print axioms` (AxCheck) of all five = `[propext, Classical.choice,
>   Quot.sound]` (clean-three), no `sorryAx`.
> - **Deferred / remaining for `hstep2` close.** Pieces 4 + 5a + 5b (the three germs above). The
>   `hstep2` sorry at `DeepestL2Wiring.lean:1060` is UNTOUCHED (no laundering). Decorrelated Codex
>   (xhigh, `codex/piece4-decomp-{prompt,answer}.md`) flagged the CHAIN-CHOICE WALL RISK: the bare
>   `Cq_s = fromBlocks (1+gaugeReadX_s) Y_s Z_s T_s` chain (which `deepestCoreF_coreAbsorb_eq_prodSchur`
>   forces on the untwisting side) was numerically FALSE for `Score` at L=2 — the actual layer pivots
>   `deepBlkA_s + gaugeReadX_s` entered; the endpoint frames `P0,QL` are removed by
>   `schur_frame_transform` but the `deepBlk` constants are not. So the chain/readback statement for
>   `huntwist` (`blockSchur(partProd C L) = ScoreSchur`) must be LOCKED before piece 4's `K = Kcoup C`
>   is built — pieces 4 and 5a are co-designed, not independently separable.
> - **Status.** sorry-free + green (`scripts/lb DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeGen`,
>   `scripts/lb DLNFibre.DLN.RLCT.AxCheck`). Name-clash `rg`-gated (all six top-level names unique across
>   `DLNFibre/`). Wired into the branch aggregator `DLNFibre.lean` + `AxCheck.lean` (feature-branch
>   single-writer allowance). NOT reviewed yet.

## Remaining work for `hstep2` (pieces 4 + 5a + 5b) — the coupled geometric bulk

Following Codex's build order (lock the chain/readback statement first):

1. **Lock the chain + readback.** Define the ℕ-indexed framed chain `C : (k:ℕ) → Matrix (r ⊕ m k)
   (r ⊕ m (k+1)) ℝ` (`m k = Fin (deepestM …)`), and state `blockSchur (partProd C L) = ScoreSchur x`.
   Resolve whether `C` needs `deepBlkA_s + X_s` (actual pivots) or bare `1 + X_s` (Codex flag: L=2 needed
   `deepBlkA`). Typecheck the `Fin L ↔ ℕ` / `castSucc`/`succ` casts. Prove `Kcoup C 0 = 0`.
2. **Piece 4.** `K s q := χ(q) • Kcoup (C q) s` (cutoff bump `χ` on the invertibility locus, à la
   `schurCutoffShift`); `hKcd` via `contDiff_contDiffBump_smul` + `ContDiffAt` on `tsupport χ`; `hK0`.
3. **Piece 5a (`huntwist`).** `deepestCoreF_coreAbsorb_eq_prodSchur` (LHS = `‖∏ S_s‖²`) → `∏(1−K_s)S_s =
   coreProd C L = blockSchur(partProd C L)` (`schur_product_ldu_rec`, `Kcoup C 0 = 0` kills the first
   correction) → `= ScoreSchur` (the readback: `prod_eq_prodAux_mul_last` +
   `rcore_eq_schur_of_corner_split` + `schur_frame_transform`, + the `Fin (H k)` cast).
4. **Piece 5b (`hreginv`).** The general-`L` E2 reg-preservation: the reg blocks of the framed product
   are invariant under the conjugate core-shear (`deepestEFull (coreAbsorb⁻¹ (Ψ (coreAbsorb q))) =
   deepestEFull q`, germ). Analog of L=2's `e2_regPreserve`. Likely the subtlest piece.
5. **Wire.** Instantiate `deepest_diffeo_bridge_gen_impl` at the L≥3 `hstep2` site (`DeepestL2Wiring.lean`
   ~1054), discharging `hKcd`/`hK0`/`huntwist`/`hreginv` from pieces 4/5a/5b, closing the sorry at :1060.

## Notes

- The bridge is stated at the WEAKEST hypotheses (no `B`/`hB`/`hwstar`): any `wstar` whose
  `split = deepestSplit … wstar` carries it to `0`. The caller instantiates
  `wstar = (paramsEquivFlat H)(deepestPoint …)`.
- `matMulCLM`/`Ψ`-hypothesis matrix norm: needs `open scoped Matrix.Norms.Elementwise` (as
  `DeepestPsiContDiff`).
