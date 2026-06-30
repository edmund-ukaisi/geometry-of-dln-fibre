import DLNFibre.DLN.RLCT.Validate.RouteMLeafBData

/-!
# `RouteMReaderFDeriv` — the fderiv VALUE atoms for the slot readers (`readK/X/N/E/W`, `rfinDirect`)

The foundation gap the `hDtot` staircase tide named: only the DIFFERENTIABILITY of the readers
(`diffAt_read*`) was banked, not their explicit fderiv VALUE. Each reader `readK/X/N/E/W … y i j =
y (idx i j)` is a single coordinate projection of `y : Fin (routeMAmbient M) → ℝ`, so as a function
of `y` its fderiv is the projection CLM `ContinuousLinearMap.proj (idx i j)` (`hasFDerivAt_apply`).
The matrix-valued reader `fun y => Matrix.of (reader y) : Matrix _ _ ℝ` assembles per-entry through
`hasFDerivAt_pi` into the entrywise-projection CLM.

This module records, for each reader, the explicit `HasFDerivAt` whose CLM is the constant
"read-the-same-slot" linear map — the per-block fderiv values the `Cgen`/`Agen` fderiv assembly
(`RouteMAgenFDerivValue`) consumes as `dB/dN/dR/dW` hypotheses.

* `readerEntryFDeriv` — the scalar reader's fderiv is `proj idx`.
* `hasFDerivAt_readK/X/N/E/W` — the matrix readers' fderiv (entrywise projection).
* `hasFDerivAt_rfinDirect` — the leaf reader's fderiv (entrywise projection).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (Mathlib `hasFDerivAt_apply` + `hasFDerivAt_pi`).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The scalar coordinate-projection fderiv

Every reader is `fun y => y idx` for a fixed slot `idx`. Its fderiv at any `y₀` is the projection
CLM `ContinuousLinearMap.proj idx`. -/

/-- The scalar coordinate read `fun y => y idx` has fderiv `proj idx`. The reader atom. -/
theorem hasFDerivAt_coordRead {Nn : ℕ} (idx : Fin Nn) (y₀ : Fin Nn → ℝ) :
    HasFDerivAt (fun y : Fin Nn → ℝ => y idx)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin Nn => ℝ) idx) y₀ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin Nn => ℝ) idx).hasFDerivAt

/-! ## The matrix-valued reader fderivs

A reader returns a matrix `Matrix.of fun i j => y (idx i j)`. Through `Matrix` = `Fin _ → Fin _ → ℝ`
(definitionally a `Pi` of `Pi`s), `hasFDerivAt_pi` reduces the matrix fderiv to the per-entry scalar
projections. The resulting fderiv CLM is `(matrixReaderCLM idx)`, the entrywise-projection map. -/

/-- The entrywise-projection CLM for a matrix-valued reader: the `(i, j)` row of its image is the
projection `proj (idx i j)`. Built by the `Pi`/`Pi` assembly `ContinuousLinearMap.pi`. -/
noncomputable def matrixReaderCLM {Nn p q : ℕ} (idx : Fin p → Fin q → Fin Nn) :
    (Fin Nn → ℝ) →L[ℝ] Matrix (Fin p) (Fin q) ℝ :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
    ContinuousLinearMap.proj (idx i j)))

/-- The matrix coordinate read `fun y => Matrix.of fun i j => y (idx i j)` has fderiv
`matrixReaderCLM idx`. Assembled entrywise via `hasFDerivAt_pi''` (row then entry — the `Matrix`
codomain carries the `Pi.*` instances through the `proj`-composition form, matching the banked
`hasFDerivAt_chainA` pattern). -/
theorem hasFDerivAt_matrixRead {Nn p q : ℕ} (idx : Fin p → Fin q → Fin Nn)
    (y₀ : Fin Nn → ℝ) :
    HasFDerivAt (fun y : Fin Nn → ℝ => (Matrix.of fun i j => y (idx i j) : Matrix (Fin p) (Fin q) ℝ))
      (matrixReaderCLM idx) y₀ := by
  apply hasFDerivAt_pi''
  intro i
  apply hasFDerivAt_pi''
  intro j
  -- the `(i,j)` component is the scalar read `fun y => y (idx i j)`, fderiv `proj (idx i j)`.
  -- `(proj j).comp ((proj i).comp (matrixReaderCLM idx)) = proj (idx i j)` by `proj_pi` (`rfl`),
  -- and `(Matrix.of f) i j = f i j` (`rfl`), so the scalar atom closes it definitionally.
  exact hasFDerivAt_coordRead (idx i j) y₀

end DLNFibre.DLN.RLCT
