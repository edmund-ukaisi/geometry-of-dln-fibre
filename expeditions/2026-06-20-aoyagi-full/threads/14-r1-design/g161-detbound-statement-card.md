# Statement card — IFT det-bound bedrock (#44c, the gauge-absorption RLCT-peel input)

The analytic data crux2's `rlctAtOn_boundedUnit_localHomeomorph` (#72) consumes, derived from the
clean implicit-function-theorem form a `C¹` local diffeo provides. Feeds `regAbsorb_rlct` /
`coreAbsorb_rlct` (both gauge absorptions are local diffeos of this form).

> **Claim (det ≠ 0).** A continuous-linear-equiv `f' : M ≃L[ℝ] M`, coerced to a continuous linear
> map, has nonzero determinant.
>
> - **Lean:** `DLNFibre.DLN.RLCT.clm_det_ne_zero`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeDiffeo.lean` @ `bb89c4b`)
> - **Gloss.** `(f' : M →L[ℝ] M).det ≠ 0`. The coerced linear map IS `f'.toLinearEquiv`, whose
>   determinant is a unit (`LinearEquiv.isUnit_det'`), hence nonzero.
> - **Proved.** Unconditionally (no finite-dimensionality needed — `omit`ted).
> - **Cited / Assumed / Deferred.** none.
> - **Status.** sorry-free, axioms `{propext, Classical.choice, Quot.sound}`.

> **Claim (det continuity).** For a `C¹` map `f` at `wstar`, the Jacobian-determinant-modulus
> `w ↦ |（fderiv ℝ f w).det|` is continuous at `wstar`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.continuousAt_abs_fderiv_det`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeDiffeo.lean` @ `bb89c4b`)
> - **Gloss.** From `ContDiffAt ℝ 1 f wstar`: `ContinuousAt (fun w => |(fderiv ℝ f w).det|) wstar`.
>   Composes `ContDiffAt.continuousAt_fderiv` (the derivative is continuous), `continuous_det`
>   (`ContinuousLinearMap.continuous_det`), and `continuous_abs`.
> - **Proved.** Unconditionally for `ContDiffAt ℝ 1`.
> - **Cited / Assumed / Deferred.** none.
> - **Status.** sorry-free, clean-three.

> **Claim (bounded-unit Jacobian datum, the #72 `hbdd`).** For a `C¹` self-map `f` whose derivative
> at `wstar` is a continuous-linear-equiv `f'`, the Jacobian-determinant-modulus is two-sidedly
> bounded on an open neighbourhood of `wstar`, with a strictly-positive lower bound.
>
> - **Lean:** `DLNFibre.DLN.RLCT.boundedUnit_fderiv_det`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeDiffeo.lean` @ `bb89c4b`)
> - **Gloss.** From `ContDiffAt ℝ 1 f wstar` and `HasFDerivAt f (f' : M →L[ℝ] M) wstar`:
>   `∃ V, IsOpen V ∧ wstar ∈ V ∧ ∃ a b, 0 < a ∧ ∀ w ∈ V, a ≤ |(fderiv ℝ f w).det| ∧ |…| ≤ b`.
>   At `wstar` the value is `|f'.det| > 0` (`HasFDerivAt.fderiv` + `clm_det_ne_zero`);
>   `ContinuousAt` pulls back the open interval `(|f'.det|/2, |f'.det|+1)` to a nbhd; take its
>   interior for the open `V`.
> - **Proved.** Unconditionally for the stated `C¹` + invertible-derivative hypotheses. This is
>   EXACTLY the `hbdd` hypothesis of crux2's #72 (and `hbddsymm` by applying it to the local
>   inverse, whose derivative `f'.symm` is also a CLE). `hdetmeas` follows from continuity
>   (`Continuous.measurable`), `hderiv` from `ContDiffOn → HasFDerivAt` on `V`.
> - **Cited.** `ContinuousLinearMap.continuous_det`, `ContDiffAt.continuousAt_fderiv`,
>   `LinearEquiv.isUnit_det'` (all Mathlib v4.29).
> - **Assumed / Deferred.** none.
> - **Status.** sorry-free, clean-three.

## Role in #44c

These three discharge the `hbdd`/`hdetmeas`/`hderiv` inputs of the #72 local bounded-unit RLCT peel
from the clean IFT form (`ContDiffAt` + `HasFDerivAt` with a CLE derivative). The remaining wrapper
`rlctAtOn_comp_localDiffeo` (the IFT → #72 plumbing: build π/πsymm via
`ContDiffAt.toOpenPartialHomeomorph`, both det-bounds via `boundedUnit_fderiv_det`) is the next
layer; then `regAbsorb_rlct` / `coreAbsorb_rlct` each = one application. The det-bound is the only
analytic content of the two RLCT-peel fields — now banked.
