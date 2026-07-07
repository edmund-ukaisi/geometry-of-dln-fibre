# Statement card — #120 `hstep2` piece 3-apply: `dΨ(0) = I`

> **Claim.** The general-`L` absorbing shear `Ψ = deepestPsiCoreShear K` on the split space
> `DeepestSplit H r nGauge` has strict Fréchet derivative the **identity** at the split basepoint `0`,
> provided the coupling `K` vanishes at the basepoint (`∀ s, K_s 0 = 0`) and is strictly
> differentiable there (`∀ s, ∃ K'_s, HasStrictFDerivAt (K_s) K'_s 0`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.hasStrictFDerivAt_deepestPsiCoreShear`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiApply.lean` @ `4a99a2e8`, branch `genm-hstep2apply`)
> - **Gloss.** For a coupling family `K` with `K_s 0 = 0` (per layer `s`) and each `K_s` strictly
>   differentiable at `0`, the map `Ψ : DeepestSplit → DeepestSplit` that keeps the regular (`.1`) and
>   spectator (`.2.2`) coordinates and, on the core (`.2.1`), decodes to the reduced tuple, left-shears
>   each layer `S_s ↦ (1 − K_s q)·S_s`, and re-encodes, satisfies
>   `HasStrictFDerivAt Ψ (ContinuousLinearMap.id ℝ (DeepestSplit H r nGauge)) 0`.
> - **Proved.** The full statement, unconditionally on `L`/`H`/`r`/`nGauge`, given the two named
>   hypotheses. Assembled from banked pieces: reg/spec ⇒ `fst`, `snd ∘ snd`; core ⇒ per-layer
>   `hasStrictFDerivAt_bilinear_of_right_zero` with `B = matMulCLM`, right factor vanishing at `0`, and
>   left factor `1 − K_s 0 = 1` (`matMulCLM 1 = id`) collapsing the core-block derivative to the
>   encode∘decode = identity round-trip (core projection `q ↦ q.2.1`); `prodMk` gives derivative
>   `q ↦ (q.1, (q.2.1, q.2.2)) = q`.
> - **Assumed.** `hK0 : ∀ s, K s 0 = 0` (coupling vanishes at basepoint) and
>   `hKderiv : ∀ s, ∃ K', HasStrictFDerivAt (fun q => K s q) K' 0` (coupling strictly differentiable at
>   basepoint). Both are discharged by the concrete DLN coupling at assembly (pieces 4–5); the derivative
>   VALUE of `K` is irrelevant (absorbed by the vanishing right factor), only its existence.
> - **Cited.** None. Forced `#print axioms hasStrictFDerivAt_deepestPsiCoreShear` =
>   `[propext, Classical.choice, Quot.sound]` (clean-three, gated in `AxCheck.lean`).
> - **Deferred.** The concrete DLN coupling `K` (piece 4, controller de-risking) that discharges `hK0` +
>   `hKderiv`, and the `hstep2` assembly (piece 5) that composes this diffeo through
>   `rlctAtOn_comp_localDiffeo`. This lemma is the standalone piece-3-apply; it does not touch the
>   `hstep2` sorry in `DeepestL2Wiring`.
> - **Route.** Rewrite `Ψ` to a fully-CLE form via `paramsEquivFlatCLE_coe` + an inline `symm`-coe
>   bridge (the strict derivative needs the `ContinuousLinearEquiv` packaging, not the `MeasurableEquiv`
>   `paramsEquivFlat`); differentiate the core into `Params` via `hasStrictFDerivAt_pi''` (with the
>   fully-unfolded function-form `F'` so the global `Pi.normedAddCommGroup` synthesizes); per-layer feed
>   the banked bilinear scaffold; compose the CLE round-trip; `prodMk` the three components;
>   `ContinuousLinearMap.ext` to identify the total with `id`.
> - **Status.** sorry-free + reviewed. Full `DLNFibre` green-gated (EXIT=0, name-clash gate passed).
>   Reviewer fidelity check: **PASS (survived)**, corroborated by decorrelated Codex xhigh — statement
>   faithful, hypotheses honest and non-vacuous (in-Lean witnesses `K = 0` and `K_s q = φ(q)·1` shown),
>   no over/under-claim, axiom-clean (force-recompiled `#print axioms`). Reviewer nuance (not a defect):
>   `∀ s, K_s 0 = 0` is the clean/usable hypothesis, not literally weakest — the derivative only needs
>   `K_s 0` to left-annihilate the layer's core matrices, which collapses to `K_s 0 = 0` whenever the
>   reduced output width `H(s.succ) − r ≥ 1` and is immaterial otherwise; it matches the informal claim
>   and the concrete DLN coupling (pieces 4–5) supplies exactly it.

## Notes

- **`matMulCLM` normed instance.** The per-layer left factor / bilinear map needs the elementwise
  matrix norm, which is `scoped` (`Matrix.Norms.Elementwise`, `= fast_instance% Pi.normedSpace`); the
  module activates it with `open scoped Matrix.Norms.Elementwise`. Verified compatible with `matMulCLM`'s
  baked-in instance (the per-layer mechanism feed typechecks).
- **Name-clash avoided.** `paramsEquivFlatCLE_symm_coe` already exists identically in
  `DeepestDiffeoBridgeL2.lean` (same namespace, in the aggregator closure); to avoid an
  `environment already contains` clash the `symm`-coe bridge is inlined as a local `have hsymm` in the
  proof rather than a top-level lemma. (A future cleanup could lift the single copy to
  `Foundations/ParamsFlatLinear.lean` next to `paramsEquivFlatCLE_coe` and delete the
  `DeepestDiffeoBridgeL2` copy — out of scope for this tide.)
