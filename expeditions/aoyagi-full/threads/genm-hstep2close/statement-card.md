# Statement card — #120 `hstep2` piece 2: `Ψ` is globally `ContDiff ℝ ⊤` (+ the local-diffeo capstone)

> **Claim.** The general-`L` absorbing shear `Ψ = deepestPsiCoreShear K` on the split space
> `DeepestSplit H r nGauge` is globally `ContDiff ℝ ⊤` whenever the coupling family `K` is
> (`∀ s, ContDiff ℝ ⊤ (K_s ·)`). Combined with the banked piece-3-apply (`dΨ(0) = I`) and the banked
> basepoint (`Ψ 0 = 0`), this gives the exact triple the RLCT-invariance bridge
> `rlctAtOn_comp_localDiffeo` consumes: `ContDiff ⊤ Ψ ∧ HasStrictFDerivAt Ψ id 0 ∧ Ψ 0 = 0`.
>
> - **Lean:**
>   - `DLNFibre.DLN.RLCT.contDiff_deepestPsiCoreShear`
>   - `DLNFibre.DLN.RLCT.deepestPsiCoreShear_isLocalDiffeoAt`
>   - (`lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiContDiff.lean`, branch `genm-hstep2close`)
> - **Gloss.** `Ψ : DeepestSplit → DeepestSplit` keeps the regular (`.1`) and spectator (`.2.2`)
>   coordinates and, on the core (`.2.1`), decodes to the reduced-core tuple, left-shears each layer
>   `S_s ↦ (1 − K_s q)·S_s`, and re-encodes. `contDiff_deepestPsiCoreShear`: given each `K_s` globally
>   `ContDiff ⊤`, `Ψ` is globally `ContDiff ⊤`. `deepestPsiCoreShear_isLocalDiffeoAt`: given `K` also
>   vanishing at `0` (`hK0`), packages the three-way conjunction feeding `rlctAtOn_comp_localDiffeo`.
>   (The strict-differentiability piece-3-apply needs is derived internally from `hKcd` via
>   `ContDiffAt.hasStrictFDerivAt`, so the interface carries only `hKcd` + `hK0` — weakest usable form.)
> - **Proved.** Both statements, unconditionally on `L`/`H`/`r`/`nGauge`, given the named `K` hypotheses.
>   Route: rewrite `Ψ` to fully-CLE form (`paramsEquivFlatCLE_coe` + the inline `hsymm` coe-bridge — same
>   as piece-3-apply); reg/spec ⇒ `contDiff_fst`, `contDiff_snd.comp contDiff_snd`; per-layer core shear
>   `(1 − K_s q)·S_s = matMulCLM (1 − K_s q) (decode q.2.1 s)` ⇒ `ContDiff.clm_apply` of the `ContDiff`
>   left factor (`(matMulCLM …).contDiff.comp (const.sub (hKcd s))`) and the decoded-layer projection;
>   `contDiff_pi'` assembles over layers; the CLE flattening re-encodes; `contDiff_fst.prodMk (… .prodMk …)`
>   assembles the three coordinates. The capstone is a `⟨_, _, _⟩` of piece 2, piece-3-apply, basepoint.
> - **Assumed.** `hKcd : ∀ s, ContDiff ℝ ⊤ (K_s ·)` (piece 2); additionally `hK0 : ∀ s, K_s 0 = 0`
>   (capstone). Both are discharged by the concrete DLN cutoff coupling at assembly (pieces 4–5). `hKcd`
>   is the global-smoothness hypothesis the concrete cutoff `Kcoup` (bump × matrix-inverse coupling)
>   supplies; the derivative-existence piece-3-apply needs is derived from `hKcd`, not assumed.
> - **Cited.** None. Forced `#print axioms` (force-recompiled scratch) of both = `[propext,
>   Classical.choice, Quot.sound]` (clean-three), no `sorryAx`.
> - **Deferred.** The concrete DLN cutoff coupling `K` (piece 4) discharging `hKcd`/`hK0`, and the
>   `hstep2` assembly (piece 5) — the untwisting `Score = coreΦ ∘ coreAbsorb ∘ Ψ` via
>   `schur_product_ldu_rec` + the `Fin (H k)` reindex, composed through `rlctAtOn_comp_localDiffeo`.
>   These two do NOT touch the `hstep2` sorry in `DeepestL2Wiring` yet — see the remaining-work note.
>   `deepest_gauge_construction` therefore still carries `sorryAx` (the L≥3 `hstep2` sorry is unchanged).
> - **Status.** sorry-free + **reviewed (fidelity PASS)**, corroborated by decorrelated Codex — both
>   statements faithful, `hKcd` non-vacuous (in-Lean witness `K = 0`), axiom-clean-three (force-recompiled
>   `#print axioms`, no `sorryAx`), card honest (does not claim `hstep2` closed; the sorry is unchanged).
>   The reviewer's minimality nit (`hKderiv` redundant) is **applied** — the capstone now carries only
>   `hKcd` + `hK0`. Name-clash `rg`-gated (both names unique across `DLNFibre/`). NOT yet in the aggregator
>   `DLNFibre.lean` (single-writer — controller wires the import after `DeepestPsiApply`).

## Remaining work for `hstep2` (pieces 4 + 5) — the corrected architecture

The L≥3 `hstep2` sorry (`DeepestL2Wiring.lean:1060`) is `rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`,
with `Φscore x = Sreg x + Score x`, `Φcore x = Sreg x + deepestCoreF (coreAbsorb (split x)).2.1`,
`Sreg x = ∑ (regStraighten (split x)).1²`, `wstar = paramsEquivFlat (deepestPoint)`.

**The assembly diffeo is the CONJUGATE `g = coreAbsorb.symm ∘ Ψ ∘ coreAbsorb`, not `Ψ` directly.**
This is the key correction (it mirrors the L=2 `…Conj` machinery — `psiSplitRawL2CoreConj`,
`deepestCoreAbsorbConj`, `schurCutoffShiftConj` — which are precisely the coreAbsorb-conjugated forms).
Rationale: `coreAbsorb` shifts the raw core `T_s` to the per-layer Schur core `S_s = T_s − Z_s A_s⁻¹ Y_s`
(the additive `schurCutoffShift`), so `deepestCoreF (coreAbsorb q).2.1 = ‖∏_s S_s‖²`; the target `Score`
is `‖blockSchur(framed product)‖² = ‖coreProd‖² = ‖∏_s (1−K_s) S_s‖²` (WITH the interspersed
corrections). To turn `∏ S_s` into `∏ (1−K_s) S_s` the shear must act on the ALREADY-corrected core,
i.e. `Ψ` composed AFTER `coreAbsorb`. In the assembly:

- `Φcore = Fcore ∘ split`, `Fcore q := Sreg-of q + deepestCoreF (coreAbsorb q).2.1`.
- `Φscore = (Fcore ∘ g) ∘ split` as a germ at `wstar` — because `Fcore (g q) = Sreg-of q + deepestCoreF
  (coreAbsorb (g q)).2.1`, `coreAbsorb (g q) = Ψ (coreAbsorb q)` (the `coreAbsorb.symm`/`coreAbsorb`
  cancel), and `deepestCoreF (Ψ (coreAbsorb q)).2.1 = ‖∏ (1−K_s) S_s‖² = Score` (the untwisting), while
  `g` fixes reg so `Sreg-of (g q) = Sreg-of q`.
- Then: transport both through `split` (banked `rlctAtOn_comp_homeomorph`, `split wstar = 0`) to
  `rlctAtOn (Fcore ∘ g) 0` vs `rlctAtOn Fcore 0`, and close with `rlctAtOn_comp_localDiffeo` (F = Fcore,
  f = g). `g` is a local diffeo at `0`: `ContDiff ⊤` (this card's piece 2 for Ψ, + banked
  `contDiff_coreShearHomeo`/`_symm` for coreAbsorb^±), `dg(0) = id` (chain of `dΨ(0)=id` [capstone] and
  `d(coreAbsorb^±)(0)=id` [the forward analog of the banked `hasStrictFDerivAt_coreShearHomeo_symm_zero`,
  since `D(schurCutoffShift)(0)=0`]), `g 0 = 0`.

**Piece 4 (concrete `K`).** `K_s q := Kcoup (C q) k` (with the `Fin (H k) ↔ (r ⊕ Fin (deepestM k))` width
cast), where `C q` is the framed DLN chain read off the split point `q` — the same per-layer `2×2`-block
`fromBlocks (A_s) (Y_s) (Z_s) (T_s)` structure that `Score`'s `Mw` decomposes into (via
`framedParamsPivot`/`deepestEFull`/`gaugeReadX/Y/Z`). Cutoff by the established bump so it is globally
`ContDiff` (`hKcd`). `hK0`: at `q = 0` the off-pivot blocks `Y_s`, `Z_s` vanish, so `(P_k)₁₂(0) = 0` and
`K_s 0 = 0`. (These `hKcd` + `hK0` are the only two the capstone consumes — the derivative existence is
already derived from `hKcd` inside `deepestPsiCoreShear_isLocalDiffeoAt`.)

**Piece 5 (untwisting).** `deepestCoreF (Ψ (coreAbsorb q)).2.1 = Score` reduces to
`prod (deepestM) (fun s => (1−K_s)·S_s) = coreProd (C q) L = blockSchur (partProd (C q) L)` — the banked
`schur_product_ldu_rec` — plus the `Fin (H k)` cast-grind connecting the DLN `prod`/`prodAux`
(`Fin (H k)` widths) to the abstract `partProd`/`coreProd` (`r ⊕ Fin (deepestM k)` types) via
`reindex_mul_fromBlocks` / `prod_eq_prodAux_mul_last`, and the `rcore_eq_schur_of_corner_split` corner
step (the `+1`). This is the genuine remaining labor (comparable in size to the L=2 `DeepestDiffeoBridgeL2`).

## Notes

- **`matMulCLM` normed instance.** Same as piece-3-apply: needs `open scoped Matrix.Norms.Elementwise`.
- **Import.** `DeepestPsiContDiff` imports `DeepestPsiApply` (for the capstone's piece-3-apply feed).
  Controller: add `import DLNFibre.DLN.RLCT.Validate.DeepestPsiContDiff` after `DeepestPsiApply` in
  `DLNFibre.lean` (line ~730) and add both names to `AxCheck.lean` as load-bearing.
