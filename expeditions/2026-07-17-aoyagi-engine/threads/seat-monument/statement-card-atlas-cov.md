# Statement card — the atlas change-of-variables (MONUMENT BUILD 1)

> **Claim.** For a certified resolution **atlas** `res : Resolution F x₀` of the sum-of-squares loss
> `∑ᵢ Fᵢ²` at the deepest point `x₀`, the local RLCT is the **minimum over the charts** of the
> per-chart weighted RLCTs at their origins:
> `rlctAt (∑Fᵢ²) x₀ = ⨅_c wrlctAt |det Dg_c| (∑(Fᵢ∘g_c)²) 0` (worked.tex:178).
>
> - **Lean:** `DLNFibre.Core.Aoyagi.rlctAt_sumSqFam_eq_iInf_charts`
>   (`lean/DLNFibre/Core/Aoyagi/ProductResolution.lean`; branch
>   `worktree-agent-a34130c87db24f302`, off `origin/worktree-agent-a045bc10366db8bcf` @ a7db69705 —
>   commit SHA pending controller integration).
> - **Gloss.** `rlctAt (sumSqFam F) x₀ = Finset.univ.inf' res.hne (fun c ↦ wrlctAt (res.charts c).jacWeightFn (sumSqFam (fun i ↦ F i ∘ (res.charts c).g)) 0)`.
>   The supremum of exponents `c ≥ 0` making `(∑Fᵢ²)^{-c}` locally integrable at `x₀` equals the
>   `Finset.inf'` over the atlas' charts of the same threshold for the Jacobian-weighted pulled-back
>   loss `|det Dg_c|·(∑(Fᵢ∘g_c)²)^{-c}` at the chart origin `0`.
> - **Proved (unconditionally, from the `Resolution`/`Chart` fields).**
>   The local admissible set at `x₀` equals `[0, R)` with `R = ⨅_c T_c`, `T_c` the chart's boxed
>   threshold `monomialThreshold (bexp k₀) jac hbind`:
>   - **≤ leg** (`Chart.mem_wLocalAdmissible_of_localAdmissible`): a source ball `s ⊆ g_c⁻¹ s₀ ∩ nbhd`
>     has `g_c '' s ⊆ s₀`; the **InjOn-off-null area formula**
>     (`lintegral_image_eq_lintegral_abs_det_fderiv_mul_of_injOn_off_null`, `AreaFormula.lean`) turns
>     `∫_s |det Dg_c|·(K∘g_c)^{-c}` into `∫_{g_c '' s} K^{-c} ≤ ∫_{s₀} K^{-c} < ∞`, so global
>     admissibility forces `c < T_c` in every chart.
>   - **≥ leg** (`Resolution.mem_localAdmissible_of_lt`): for `c < R`, each chart's compact domain is
>     integrable — per-point local integrability at every `p ∈ dom_c` from **off-origin Object C**
>     (`monomialSumSq_integrableAtFilter_of_lt`, the worst singularity is at `0` so `c < T_c` suffices)
>     via Object-A-at-`p` reduction, plus `LocallyIntegrableOn.integrableOn_isCompact`; the area
>     formula pushes each `∫_{dom_c}` down to `∫_{g_c '' dom_c}`; the a.e.-cover `hcover`
>     (subadditivity over the finite atlas union) transfers integrability onto `U ∈ 𝓝 x₀`.
>   Then `rlctAt = sSup [0,R) = R` and each `wrlctAt_c = T_c` (`Chart.wrlctAt_eq_threshold`), so the
>   `inf'` is `R`.
> - **Assumed (fields of the `Chart`/`Resolution` records, i.e. what "certified atlas" means).**
>   per-chart analytic `g` with `g 0 = x₀`; dom-wide Jacobian certificate `|det Dg| = jacWeight jac·unit`
>   (`hjac`); dom-wide two-sided ideal identity `⟨F∘g⟩ = ⟨monomialFam bexp⟩` (`hideal_fwd`/`hideal_bwd`
>   as `RegionRepresents` on `nbhd`); divisibility chain `hchain`; binding-axis nonemptiness `hbind`;
>   a.e.-injectivity off a null exceptional locus (`hexcep_null`/`hg_inj`); compact domains `dom` with
>   the a.e.-cover `hcover`. These are the hypotheses Aoyagi's proper resolution supplies.
> - **Cited.** none — the proof rests only on `[propext, Classical.choice, Quot.sound]` (verified via
>   `#print axioms`). Mathlib's area formula (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) and
>   its null-image lemma are library results, not `@[cited]` monuments.
> - **Deferred.** none for THIS leaf. (Separately, the *existence* of a certified atlas for the DLN
>   loss — `exists_coreResolution` — is a distinct monument and remains a `sorry` in the DLN layer;
>   it is NOT part of this theorem, which takes `res` as a hypothesis.)
> - **Status.** REVIEWED (rev-cov-fidelity PASS, 2026-07-21; `#print axioms` = `[propext, Classical.choice, Quot.sound]`; integrated at the expedition tip).

## Downstream footprints (verified clean-three, `#print axioms`)

Discharging this leaf makes the whole engine value chain sorry-free automatically:

- `DLNFibre.Core.Aoyagi.rlctAt_sumSqFam_eq_iInf_charts` — `[propext, Classical.choice, Quot.sound]`
- `DLNFibre.Core.Aoyagi.Resolution.two_mul_rlctAt_eq_divisorMin` — `[propext, Classical.choice, Quot.sound]`
- `DLNFibre.Core.Aoyagi.Resolution.divisorMin_eq_cCodim` — `[propext, Classical.choice, Quot.sound]`
- `DLNFibre.Core.Aoyagi.Resolution.two_mul_rlctAt_eq_cCodim` (the engine value headline `2·rlct = cCodim`)
  — `[propext, Classical.choice, Quot.sound]`

## Reusable infrastructure banked alongside

- **`AreaFormula.lean`** — `lintegral_image_eq_lintegral_abs_det_fderiv_mul_of_injOn_off_null`: the
  InjOn-off-null relaxation of Mathlib's area-formula `lintegral` equality (injective off a null set;
  the differentiable image of a null set is null). General over any finite-dim space with a Haar
  measure. This is the "named remainder (b)" Waypoint owed.
- **`MonomialRLCT.lean`** (additive) — `monomialSumSq_integrableAtFilter_of_lt` (off-origin S2
  convergence, base point `p`), `monomialSumSq_not_integrableAtFilter_of_exists_le` (origin
  divergence), `monomialSumSq_wLocalAdmissible_eq` (origin set form `= [0,T)`),
  `monomial_forall_neg_one_lt_iff_lt_threshold` (the boxed-min arithmetic),
  `exists_unit_sumSqFam_monomial_strong` (global `Continuous U`, `1 ≤ U`), `monomialThreshold_pos`.
- **`ProductResolution.lean`** — `Chart.jacWeight_form_at`, `Chart.wLocalAdmissible_swap`
  (Object-A at an arbitrary base point of the region), `Chart.wLocalAdmissibleExponents_eq_Ico`,
  `Chart.wrlctAt_eq_threshold`, `Chart.integrableAtFilter_of_lt`,
  `Chart.mem_wLocalAdmissible_of_localAdmissible`, `Resolution.mem_localAdmissible_of_lt`.
