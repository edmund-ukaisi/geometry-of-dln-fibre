import DLNFibre.DLN.RLCT.Foundations.ParamsFlat
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# `DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear` — `paramsEquivFlat` as an ℝ-linear iso

`paramsEquivFlat H : Params H ≃ᵐ (Fin (flatDim H) → ℝ)` is a coordinate **reshape + reindex** — it
is ℝ-LINEAR as a function (two `Sigma.uncurry` currying steps then an `arrowCongr'` reindex), but in
`ParamsFlat.lean` it is packaged only as a `MeasurableEquiv` (+ a proven homeomorphism). For the
genuine geometric change-of-variables of a chart `phi = paramsEquivFlat ∘ (polynomial matrix map)`,
the chain rule needs `paramsEquivFlat`'s `fderiv` as a `ContinuousLinearMap`, which the
`MeasurableEquiv` packaging does not provide.

This module supplies the missing **linear** packaging:
- `paramsEquivFlatLinear H : Params H ≃ₗ[ℝ] (Fin (flatDim H) → ℝ)`, the `LinearEquiv` built from the
  `LinearEquiv` versions of the same three pieces (`piCurry` ×2, `funCongrLeft`);
- `paramsEquivFlatCLE H : Params H ≃L[ℝ] (Fin (flatDim H) → ℝ)`, its `ContinuousLinearEquiv`;
- the agreements `paramsEquivFlatLinear_coe` / `paramsEquivFlatCLE_coe` (SAME underlying function as
  `paramsEquivFlat H`, by `rfl`);
- the constant fderiv `hasFDerivAt_paramsEquivFlat` (the reindex CLM is the flattening's fderiv);
- the sup-norm `NormedAddCommGroup`/`NormedSpace`/`FiniteDimensional` on `Params H` (`inst*Params`),
  `rfl`-compatible with the existing product topology (`instTopologicalSpaceParams_eq_norm`).

This is the per-node measure-plumbing atom the general-`M` `hfin` certificate flags (cost driver 2);
it is shared across all binding nodes, so it is built once here. It is fully general in `H`/`L` (not
specialised to `(3,3,4)`). It closes the "no `ContinuousLinearEquiv`/fderiv for the reindex" blocker
that stalled the genuine Jacobian change-of-variables; what remains for a node's `cov` is the inner
polynomial chart's structural Jacobian determinant, not the reindex.

## The piece correspondence (why the coes agree)

`paramsEquivFlat H = arrowCongr' (Fintype.equivFin (FlatIdx H)) (refl ℝ) ∘ uncurry ∘ uncurry`
where each `MeasurableEquiv.piCurry.symm` has coe `Sigma.uncurry` and `arrowCongr' hα (refl ℝ)` has
coe `· ∘ hα.symm` (`Equiv.arrowCongr'`). The linear version composes
`funCongrLeft ℝ ℝ (Fintype.equivFin (FlatIdx H)).symm` (coe `· ∘ (equivFin).symm`, matching the
reindex) after the two `(LinearEquiv.piCurry _).symm` (coe `Sigma.uncurry`). Both reduce to the SAME
function.
-/

open MeasureTheory
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- `Params H` inherits the product ℝ-module structure (definitionally a `Pi` of `Pi`s of `ℝ`). The
algebraic counterpart of `instTopologicalSpaceParams`/`instMeasureSpaceParams` (`Rlct.lean`), needed
to state the linear flattening. -/
noncomputable instance instAddCommGroupParams (H : Fin (L + 1) → ℕ) : AddCommGroup (Params H) :=
  inferInstanceAs (AddCommGroup (∀ s : Fin L, (Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ))

/-- `Params H` inherits the product ℝ-module structure. -/
noncomputable instance instModuleParams (H : Fin (L + 1) → ℕ) : Module ℝ (Params H) :=
  inferInstanceAs (Module ℝ (∀ s : Fin L, (Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ))

/-- `Params H` inherits the **sup-norm** `NormedAddCommGroup` (the product norm on the unfolded
`Pi`-of-`Pi`-of-`ℝ`; `Matrix` is definitionally a function space). Its induced topology is
DEFINITIONALLY the existing `instTopologicalSpaceParams` (the product topology) — no diamond — so
the norm structure is compatible with all downstream `Params`-topology / measure facts. This is what
lets `paramsEquivFlat` carry an fderiv (it needs both endpoints normed). -/
noncomputable instance instNormedAddCommGroupParams (H : Fin (L + 1) → ℕ) :
    NormedAddCommGroup (Params H) :=
  inferInstanceAs
    (NormedAddCommGroup (∀ s : Fin L, (Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ))

/-- `Params H` inherits the product `NormedSpace ℝ` (compatible with `instModuleParams`). -/
noncomputable instance instNormedSpaceParams (H : Fin (L + 1) → ℕ) :
    NormedSpace ℝ (Params H) :=
  inferInstanceAs (NormedSpace ℝ (∀ s : Fin L, (Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ))

/-- `Params H` is finite-dimensional over ℝ (a finite product of finite matrices). -/
instance instFiniteDimensionalParams (H : Fin (L + 1) → ℕ) :
    FiniteDimensional ℝ (Params H) :=
  inferInstanceAs
    (FiniteDimensional ℝ (∀ s : Fin L, (Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ))

/-- The norm-topology on `Params H` is the existing product topology (`rfl`): the
`NormedAddCommGroup` instance does not introduce a competing topology. -/
theorem instTopologicalSpaceParams_eq_norm (H : Fin (L + 1) → ℕ) :
    (instNormedAddCommGroupParams H).toMetricSpace.toUniformSpace.toTopologicalSpace
      = instTopologicalSpaceParams H := rfl

/-- **`paramsEquivFlat` as an ℝ-linear equivalence** `Params H ≃ₗ[ℝ] (Fin (flatDim H) → ℝ)`. The
`LinearEquiv` mirror of `paramsEquivFlat` (`ParamsFlat.lean`): two `LinearEquiv.piCurry` currying
steps (`.symm`, collapse the `(s, i, j)` nesting to `FlatIdx H`) then the reindex
`LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin (FlatIdx H)).symm`. Same underlying function as
`paramsEquivFlat H` (`paramsEquivFlatLinear_coe`), now carrying ℝ-linearity for the fderiv/`det`. -/
noncomputable def paramsEquivFlatLinear (H : Fin (L + 1) → ℕ) :
    Params H ≃ₗ[ℝ] (Fin (flatDim H) → ℝ) :=
  (LinearEquiv.piCurry ℝ
      (fun (s : Fin L) (_ : Fin (H s.castSucc)) => Fin (H s.succ) → ℝ)).symm.trans
    ((LinearEquiv.piCurry ℝ (fun (q : FlatRowIdx H) (_ : Fin (H q.1.succ)) => ℝ)).symm.trans
      (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin (FlatIdx H)).symm))

/-- **Agreement: the linear iso has the SAME underlying function as `paramsEquivFlat`.** Each
`LinearEquiv.piCurry.symm` coe is `Sigma.uncurry` (matching `MeasurableEquiv.piCurry.symm`), and
`funCongrLeft ℝ ℝ e` coe is `· ∘ e` with `e = (Fintype.equivFin _).symm` (matching `arrowCongr' hα
(refl ℝ)`, whose coe is `· ∘ hα.symm`). So the two compositions are the same function. -/
theorem paramsEquivFlatLinear_coe (H : Fin (L + 1) → ℕ) :
    ⇑(paramsEquivFlatLinear H) = ⇑(paramsEquivFlat H) := by
  funext P
  rfl

/-- **`paramsEquivFlat` as a continuous ℝ-linear equivalence**
`Params H ≃L[ℝ] (Fin (flatDim H) → ℝ)`, via `LinearEquiv.toContinuousLinearEquiv` (both endpoints
finite-dimensional normed). Same underlying function as `paramsEquivFlat H`
(`paramsEquivFlatCLE_coe`), now an honest `ContinuousLinearEquiv` whose `toContinuousLinearMap` is
the constant fderiv of the flattening. -/
noncomputable def paramsEquivFlatCLE (H : Fin (L + 1) → ℕ) :
    Params H ≃L[ℝ] (Fin (flatDim H) → ℝ) :=
  (paramsEquivFlatLinear H).toContinuousLinearEquiv

/-- The CLE has the same underlying function as `paramsEquivFlat H`. -/
theorem paramsEquivFlatCLE_coe (H : Fin (L + 1) → ℕ) :
    ⇑(paramsEquivFlatCLE H) = ⇑(paramsEquivFlat H) := by
  rw [paramsEquivFlatCLE, LinearEquiv.coe_toContinuousLinearEquiv', paramsEquivFlatLinear_coe]

/-- **`paramsEquivFlat` has a constant fderiv** — its own `ContinuousLinearMap` (the flattening is
ℝ-linear). The chain-rule ingredient for differentiating any chart `phi = paramsEquivFlat ∘ g`: the
outer factor contributes the reindex CLM `(paramsEquivFlatCLE H).toContinuousLinearMap`. -/
theorem hasFDerivAt_paramsEquivFlat (H : Fin (L + 1) → ℕ) (P : Params H) :
    HasFDerivAt (paramsEquivFlat H)
      ((paramsEquivFlatCLE H).toContinuousLinearMap) P := by
  have h : HasFDerivAt (⇑(paramsEquivFlatCLE H))
      ((paramsEquivFlatCLE H).toContinuousLinearMap) P :=
    (paramsEquivFlatCLE H).toContinuousLinearMap.hasFDerivAt
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with Q
  rw [paramsEquivFlatCLE_coe]

end DLNFibre.DLN.RLCT
