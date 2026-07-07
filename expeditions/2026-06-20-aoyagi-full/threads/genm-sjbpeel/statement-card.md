# Statement card — `sjBoundaryPeel` (the (S,J)-peel cover+measure assembly)

> **Claim.** For a `≥ 3`-width chain `M` and `c' < ½·minAdm M`, the `M` layer-product box integral is
> bounded by the finite sum, over pivot cuts `t = 1..min(M₀,M₁)` and pivot charts `(ρ,κ)`, of the
> per-`(t,ρ,κ)`-chart peeled integrals `gammaPeelIntegral M t ρ κ c'` (constant `1`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.sjBoundaryPeel`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJResolution.lean` @ `f4e06946`)
> - **Gloss.** `routeMLayerBoxIntegral M c' 1 ≤ ∑_{t ∈ Icc 1 (min M₀ M₁)} ∑_{ρ : Fin t ↪ Fin M₀}
>   ∑_{κ : Fin t ↪ Fin M₁} gammaPeelIntegral M t ρ κ c'`. `gammaPeelIntegral M t ρ κ c'` is the
>   tail-outer front-factor fibre integral `∫_{A' ∈ box(tail)} ∫_{A₀ ∈ matBox ∩ pivotChart ρ κ}
>   frobSq(A₀·prod(tailChain M) A')^{−c'}`.
> - **Proved.** The full inequality, unconditionally, for every `M : Fin (L+1+1+1) → ℕ` and `c' : NNReal`.
>   The proof is a pure cover inequality:
>   1. **product form** — `routeMLayerBoxIntegral M c' 1` = the product integral over `matBox ×ˢ box(tail)`
>      (measure-preserving front-split `routeMLayerBoxIntegral_front_split` / `eFront` +
>      `setLIntegral_comp_preimage_emb`);
>   2. **null rank-0 point** — `{A₀ = 0}` (`= {rank A₀ = 0}`) is a single `volume`-null point, so
>      `matBox ×ˢ box =ᵐ (matBox ∩ {1 ≤ rank}) ×ˢ box`;
>   3. **finite cover** — `{1 ≤ rank} = ⋃_{ρ,κ} pivotChart ρ κ` (`pivotLocus_eq_iUnion 1`), distributed
>      over `×ˢ box` (`Set.iUnion_prod_const`) and bounded by subadditivity (`lintegral_iUnion_le`);
>   4. **chart identification** — each product chart integral `= gammaPeelIntegral M 1 ρ κ c'`
>      (`setLIntegral_prod_symm`);
>   5. **embed** — the `t = 1` block is one summand of the `Icc 1 min` sum (`Finset.single_le_sum`,
>      `1 ≤ min` from `min > 0`).
>   The `min(M₀,M₁) = 0` edge is handled by contradiction: there `minAdm M = 0`
>   (`minAdm_le_minAdm_redChain_min` + `minAdm_cons_zero`), so `c' < ½·0` is unsatisfiable.
>   Steps 2–4 are packaged in the reusable bedrock helper
>   `DLNFibre.DLN.RLCT.frontBox_pivotCover_le` (product-level `t = 1` pivot cover for any measurable
>   integrand on `(Fin m → Fin n → ℝ) × β`, `m,n ≥ 1`).
> - **Assumed.** None beyond the stated hypotheses (`3`-width chain arity `L+1+1+1`, `c' < ½·minAdm M`).
> - **Cited.** None. The two mathematical hearts are banked in-repo (`pivotChartCover_matBox_le_sum`
>   pattern, `minAdm_cons_zero`); the missing Mathlib lemma `A.rank = 0 → A = 0` (v4.29 ships only the
>   converse `Matrix.rank_zero`) is proved locally inside `frontBox_pivotCover_le` via
>   `Submodule.finrank_eq_zero` + `LinearMap.range_eq_bot` + `Matrix.toLin'` injectivity.
> - **Deferred.** None for this statement. The peel is a *cover* bound only; the *finiteness* of each
>   `gammaPeelIntegral M t ρ κ c'` is the separate, deeper `sjJointResolution` (still a named sorry, not
>   touched here). The faithful cross-coupled Schur form / measure-preserving shear live there, not here.
> - **Route.** (from `genm-sjrescope`'s report + decorrelated Codex xhigh + a fidelity reviewer, all
>   confirming TRUE-provable.) The 5-step product route above; deviations from the spawn brief's
>   "5 steps" are cosmetic (the null step is done via `setLIntegral_congr` on an a.e.-set equality with
>   `Measure.prod_prod` for the null product set, rather than a `NoAtoms`-instance singleton on the whole
>   product; the pivot cover is factored into `frontBox_pivotCover_le` so it is reusable and the
>   `A.rank=0→A=0` lemma is proved once, inline).
> - **Status.** sorry-free (axiom-clean `[propext, Classical.choice, Quot.sound]`, forced `#print axioms`).

## Mathlib lemmas used (v4.29 pin)

- `A.rank = 0 → A = 0`: `Submodule.finrank_eq_zero` (`finrank R S = 0 ↔ S = ⊥`, finite submodule) +
  `LinearMap.range_eq_bot` (`range f = ⊥ ↔ f = 0`) + `Matrix.toLin'` (a `LinearEquiv`, hence injective)
  with `Matrix.toLin'_apply'` (`toLin' M = M.mulVecLin`) and `Matrix.mulVecLin_zero`.
- `NoAtoms` on the matrix `volume`: the `Measure.pi` instance
  `instance … : NoAtoms (volume : Measure (∀ i, α i))` (`MeasureTheory/Constructions/Pi.lean`, needs
  `Nonempty (Fin m)`, `Nonempty (Fin n)` — supplied from `m, n ≥ 1`), bottoming out at
  `Real.noAtoms_volume`; used via `measure_singleton` + `Measure.prod_prod`.

## Build / verification

- `scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJResolution` — green.
- Forced `#print axioms sjBoundaryPeel` / `frontBox_pivotCover_le`:
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
- `scripts/sorries`: `sjBoundaryPeel` gone; only `sjJointResolution` remains in the module (2 → 1).
- LoC delta: `+132 / −3` in `RouteMSJResolution.lean` (helper `frontBox_pivotCover_le` + the peel proof).
