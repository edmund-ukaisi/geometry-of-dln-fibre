import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution
import DLNFibre.DLN.RLCT.Validate.RouteMSJOrderedRootsMeasurable
import DLNFibre.DLN.RLCT.Validate.RouteMSJMeasurableEigenframe
import Mathlib.Analysis.Matrix.Spectrum

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJMeasurableEigendecomp` — Brick F2: `measurableEigendecomp`

The isolated Mathlib-gap primitive of Brick F. For a measurable Hermitian (real-symmetric) matrix
family `A : X → Matrix (Fin M₂) (Fin M₂) ℝ` we want a MEASURABLE sorted orthogonal diagonalization
`A z = U z · diagonal(λ↓(z)) · (U z)ᵀ`, with `λ↓` the sorted (`eigenvalues₀`) eigenvalues, themselves a
measurable function of `z`.

## Status: decomposition SKELETON — glue CLOSED, two analytic primitives ISOLATED as named sorries.

The pen-and-paper adjudication
(`expeditions/2026-06-20-aoyagi-full/threads/genm-sj5-domination/brickF-measurable-frame-adjudication.md`)
established the TRUTH-VALUE (a concrete Borel formula exists; no Kuratowski–Ryll-Nardzewski, no contour
integral). The Lean realisation, however, is a MULTI-MODULE build: a formaliser-scoping pass confirms
that EVERY primitive it needs is ABSENT from Mathlib at the v4.29 pin —

* no Weyl / eigenvalue-Lipschitz / eigenvalue-continuity lemma,
* no polynomial-root-continuity (roots as a function of coefficients),
* no Ky-Fan maximum principle `∑_{i<k} λᵢ = maxₚ tr(P·A)`,
* no compactness instance for `Matrix.unitaryGroup`,
* no measurability rider on `eigenvalues₀` (it is `Classical.choice`-built).

So each conjunct rests on a from-scratch sub-brick. This file lays the honest decomposition: the
linear-algebra GLUE (`frame_diagonalizes`) and the ASSEMBLY are CLOSED sorry-free; the two analytic
primitives (`measurableEigenvalues₀`, `exists_measurableEigenframe`) are isolated as correctly-typed
sorries carrying their build recipe, one sub-tide each.

## The decomposition

* **`measurableEigenvalues₀`** — conjunct (i). `Measurable (fun z => (hherm z).eigenvalues₀)`.
  Recipe: the Weyl-continuity brick `maxᵢ|λᵢ(A)−λᵢ(B)| ≤ ‖A−B‖_op` (⟹ Lipschitz ⟹ continuous ⟹ Borel),
  or the LSC route `Sₖ(A) = ⨆_{P rank-k orth proj} tr(P·A)` (Ky Fan) + `LowerSemicontinuous.measurable`
  with `λₖ = S_{k+1} − Sₖ`. Both need a Mathlib-absent primitive built first.

* **`exists_measurableEigenframe`** — conjunct (ii) core. A measurable orthogonal `U` whose columns are
  eigenvectors in sorted order (`A z · U z = U z · diagonal(λ↓)`). Recipe (contour-free, no KRN):
  (1) multiplicity-pattern stratification into finitely many Borel strata; (2) per-stratum Sylvester
  eigenprojection `P_a = ∏_{b≠a}(A − μ_b I)/(μ_a − μ_b)` (matrix-polynomial arithmetic + division by
  measurable eigenvalue-gaps); (3) deterministic lex-first-pivot Gram-Schmidt (`gramSchmidt` present in
  Mathlib) on each block's columns; (4) sorted concatenation. Borel, not continuous (the diabolical point
  `[[x,y],[y,−x]]` has an odd Berry phase — no global continuous frame).

* **`frame_diagonalizes`** (CLOSED) — the linear-algebra reduction: an orthogonal `U` (`Uᵀ U = 1`) whose
  columns diagonalise `A` (`A U = U · diagonal d`) gives the triple-product form `A = U · diagonal d · Uᵀ`.
  This is what turns `exists_measurableEigenframe`'s per-column eigenvector condition into the contract's
  `A z = U z · diagonal(λ↓) · (U z)ᵀ`.

* **`measurableEigendecomp`** (CLOSED assembly modulo the two primitives) — the exact F1 contract.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Matrix

/-- **Sorted-eigenvalue diagonal (contract indexing).** `sortedDiag hherm z i = eigenvalues₀`
reindexed value-preservingly from `Fin (Fintype.card (Fin M₂))` to `Fin M₂` — the decreasing
(`eigenvalues₀` is antitone) eigenvalue placed at position `i`. This is the diagonal appearing in the
F1 contract. -/
noncomputable def sortedDiag {X : Type*} {M₂ : ℕ}
    {A : X → Matrix (Fin M₂) (Fin M₂) ℝ} (hherm : ∀ z, (A z).IsHermitian) (z : X) :
    Fin M₂ → ℝ :=
  fun i => (hherm z).eigenvalues₀ (finCongr (Fintype.card_fin M₂).symm i)

/-- **The linear-algebra reduction (CLOSED).** For a square real matrix and an orthogonal `U`
(`Uᵀ * U = 1`) whose columns diagonalise `A` (`A * U = U * diagonal d`, i.e. each column of `U` is an
eigenvector of `A` with eigenvalue the matching diagonal entry), `A = U * diagonal d * Uᵀ`. The
right-inverse `U * Uᵀ = 1` follows from the left-inverse by `Matrix.mul_eq_one_comm` (square matrices).
-/
theorem frame_diagonalizes {n : ℕ} {A U : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    (hU : Uᵀ * U = 1) (hAU : A * U = U * Matrix.diagonal d) :
    A = U * Matrix.diagonal d * Uᵀ := by
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mpr hU
  calc A = A * (U * Uᵀ) := by rw [hUU, Matrix.mul_one]
    _ = (A * U) * Uᵀ := by rw [Matrix.mul_assoc]
    _ = U * Matrix.diagonal d * Uᵀ := by rw [hAU]

/-- **Brick F2 — measurable sorted eigendecomposition (F1 contract).** ASSEMBLED sorry-free from the two
imported analytic primitives — `measurableEigenvalues₀` (F2a, `RouteMSJOrderedRootsMeasurable`) and
`exists_measurableEigenframe` (F2b, `RouteMSJMeasurableEigenframe`) — via the `frame_diagonalizes`
reduction. -/
theorem measurableEigendecomp {X : Type*} [MeasurableSpace X] {M₂ : ℕ}
    (A : X → Matrix (Fin M₂) (Fin M₂) ℝ) (hA : Measurable A)
    (hherm : ∀ z, (A z).IsHermitian) :
    Measurable (fun z => (hherm z).eigenvalues₀) ∧
      ∃ U : X → Matrix (Fin M₂) (Fin M₂) ℝ,
        Measurable U ∧ (∀ z, (U z)ᵀ * U z = 1) ∧
          (∀ z, A z = U z *
            Matrix.diagonal (fun i => (hherm z).eigenvalues₀ (finCongr (Fintype.card_fin M₂).symm i))
            * (U z)ᵀ) := by
  refine ⟨measurableEigenvalues₀ A hA hherm, ?_⟩
  obtain ⟨U, hUmeas, hUorth, hUdiag⟩ :=
    exists_measurableEigenframe A hA hherm (measurableEigenvalues₀ A hA hherm)
  exact ⟨U, hUmeas, hUorth, fun z => frame_diagonalizes (hUorth z) (hUdiag z)⟩

end DLNFibre.DLN.RLCT
