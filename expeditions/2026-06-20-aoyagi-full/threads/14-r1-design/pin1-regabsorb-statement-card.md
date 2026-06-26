# Statement card — PIN 1: the deepest-point regular straightening (#44c, #82)

> **Claim.** At the rank-`r`-exact deepest point, the regular-slot straightening `regAbsorb` exists as
> a TOTAL continuous self-map of `DeepestSplit` (the (C)-fallback shape), fixing core + spectator + the
> origin, whose regular output through it carries the SAME local RLCT as the raw regular slot
> (`regAbsorb_rlct`), against the `coreAbsorb`'d core term. The map's reg-output is a pivot map
> `E_pivot : Reg × Spec → Reg`; the peel needs ONLY `dE_pivot(0) = id`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepest_regAbsorb_exists`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean` @ `67b2c13`), built from the
>   structure-independent infrastructure in `lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean`
>   (@ `67b2c13`) and the IFT det-bound bedrock in
>   `lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeDiffeo.lean`.
>
> - **Gloss.** `regAbsorb = regStraightenOf E_pivot := fun q ↦ (E_pivot (q.1, q.2.2), q.2.1, q.2.2)`.
>   `deepest_regAbsorb_exists` takes `E_pivot` + its three analytic props (`ContDiff ℝ ⊤`,
>   `HasStrictFDerivAt E_pivot (fst : Reg × Spec →L Reg) 0`, `E_pivot 0 = 0`) and the `coreAbsorb`
>   measure-preserving + slot-fix + basepoint data; it produces the five `regStraighten` obligations:
>   continuity, `0 ↦ 0`, core-fixed, spectator-fixed, and `regAbsorb_rlct`
>   `rlctAtOn (∑ (regStraighten q).1² + deepestCoreF (coreAbsorb q).2.1) 0 =`
>   `rlctAtOn (∑ q.1² + deepestCoreF (coreAbsorb q).2.1) 0`.
>
> - **Proved (sorry-free, conditional on the `E_pivot` props).**
>   - `rlctAtOn_comp_localDiffeo` — the **IFT → #72 adapter** (the detbound card's "next layer"): from
>     `ContDiff ℝ ⊤ f` + `HasStrictFDerivAt f (e : M ≃L M) wstar` + `f wstar = wstar`, conclude
>     `rlctAtOn (F ∘ f) wstar = rlctAtOn F wstar`. Extracts the IFT `OpenPartialHomeomorph`
>     (`HasStrictFDerivAt.toOpenPartialHomeomorph`), the local inverse smooth at `wstar`
>     (`OpenPartialHomeomorph.contDiffAt_symm`), the inverse derivative `e.symm`
>     (`OpenPartialHomeomorph.hasFDerivAt_symm`), bounded-unit Jacobians both ways
>     (`boundedUnit_fderiv_det`), det-modulus measurability via `measurable_fderiv` (GLOBAL, any map),
>     single working `V = source ∩ target ∩ (inverse-diff nbhd) ∩ (both det-bound sets)`, feeds
>     `rlctAtOn_boundedUnit_localHomeomorph` (#72).
>   - `regStraightenOf` + `hasStrictFDerivAt_regStraightenOf(_refl)`: the (C)-fallback total map, with
>     `dE_pivot(0) = fst` ⟹ total strict derivative `id` (= `refl`-equiv coerced), via
>     `HasStrictFDerivAt.prodMk` of the three slot components.
>   - `rlctAtOn_regAbsorb_reduce`: strips `coreAbsorb` from the coupled core term via the
>     measure-preserving `coreAbsorb.symm` conjugation (uses only `coreAbsorb` MP + fixes reg/spec +
>     origin, and `regAbsorb`'s reg-output reads reg+spec), reducing the coupled equality to the
>     decoupled `hpeel` (discharged by the adapter).
>   - `deepest_regAbsorb_exists` itself: **zero `sorry`** — the IFT/peel content of PIN 1 is complete.
>   - Clean-three axioms `{propext, Classical.choice, Quot.sound}` (modulo the `E_pivot` holes below).
>
> - **Assumed.** `IsDeepLayers` regime (`B.rank = r`, `∀ s, r ≤ H s`, `1 ≤ L`); general `L`.
>
> - **Cited.** Mathlib v4.29: `HasStrictFDerivAt.toOpenPartialHomeomorph`,
>   `OpenPartialHomeomorph.{contDiffAt_symm, hasFDerivAt_symm}`, `measurable_fderiv`,
>   `ContinuousLinearMap.continuous_det`, `LinearEquiv.isUnit_det'`. In-repo: `#72`
>   (`rlctAtOn_boundedUnit_localHomeomorph`, crux2), `boundedUnit_fderiv_det` (g161 detbound card).
>
> - **Deferred (named, the SINGLE remaining PIN-1 gap — the PIN1↔PIN2 coupling object).**
>   The shared pivot map `DLNFibre.DLN.RLCT.deepestEPivot` + its three props (`deepestEPivot_contdiff`,
>   `deepestEPivot_deriv`, `deepestEPivot_base`) are `sorry` — the concrete nonlinear straightened
>   residual whose form is load-bearing for **PIN 2**'s squeeze (`∑ E_pivot² + core ≍ loss`). PIN 1
>   needs only `dE_pivot(0) = id` (pp2 #91 certifies it, general L); PIN 2 needs the value. crux2/pp2
>   own the closed form (the product-residual `∏(I+X_s) − I` read off the gauge slots). Awaiting the
>   E_pivot-form confirmation before the `deepestEPivot` def + props are filled.
>
> - **Status.** PIN 1's analytic machinery sorry-free; the shared `deepestEPivot` (def + 3 props)
>   is the only open hole. Awaiting PIN-1↔PIN-2 coupling fidelity review (crux2) + E_pivot form.

## Notes

- **The typed `dE(0) = id`.** The ruling's "`dE(0) = id`" is precisely
  `HasStrictFDerivAt E_pivot (ContinuousLinearMap.fst ℝ Reg Spec) 0`: the reg-component's derivative is
  the projection onto the reg directions (identity on reg, zero on spectator), which makes the total
  `regStraightenOf E_pivot`'s strict derivative the identity `≃L` — the form `toOpenPartialHomeomorph`
  consumes. The nonlinear curvature (load-bearing for PIN 2) lives in the higher-order part of
  `E_pivot`, invisible to PIN 1's first-order peel.
- **Form-agnostic PIN 1.** `deepest_regAbsorb_exists` is proved for ANY `E_pivot` with those three
  props — its correctness does not depend on the concrete residual form. So pinning `deepestEPivot`
  later cannot reopen the PIN-1 peel; only the three `deepestEPivot_*` props remain.
- **No global homeomorph.** The (C) fallback keeps `regStraighten` a total continuous function (global
  measurability for `rlctAtOn_squeeze`); the local invertibility + bounded-unit Jacobian live INSIDE
  the `regAbsorb_rlct` proof via the IFT adapter, not as structure fields.
