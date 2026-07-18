import Mathlib

/-!
# Measurability of the matrix inverse

The nonsingular matrix inverse `A ↦ A⁻¹` on square matrices over `ℝ` is
Borel-measurable on the whole matrix space. It is *continuous* only on the units
(the determinant divisor blows up at `{det = 0}`), but the determinantal formula
`A⁻¹ = (Ring.inverse (det A)) • adjugate A` (`Matrix.inv_def`) exhibits it as an
entrywise product of measurable functions, hence measurable everywhere.

This is a network-free measure-theory building block (drafted for the Aoyagi-full
RLCT expedition, where the freed Schur loss carries a pivot inverse `(of P)⁻¹`
that breaks `fun_prop`'s continuity search); kept as a reusable Core lemma.

## Main result

* `measurable_matrix_of_inv_apply` — each entry `((Matrix.of P)⁻¹) i j` is a
  measurable function of the raw pi-type variable `P : Fin n → Fin n → ℝ`.

The statement is entrywise (real-valued) on purpose: the matrix-valued form
`P ↦ (Matrix.of P)⁻¹` has codomain `Matrix (Fin n) (Fin n) ℝ`, whose
`MeasurableSpace` does not resolve (there is no `MeasurableSpace (Matrix …)`
instance; only the defeq pi type `Fin n → Fin n → ℝ` carries one, and ascribing
to it flips `⁻¹` to the pointwise `Pi.instInv`, corrupting the meaning). Every
downstream measurability proof reduces to entries via `measurable_pi_iff` and
expands matrix products with `Matrix.mul_apply`, so the entrywise form composes
directly.

## Strategy

`A⁻¹ = (Ring.inverse (det A)) • adjugate A` (`Matrix.inv_def`). The determinant
and each adjugate entry are polynomial in the entries, hence continuous
(`Continuous.matrix_det`, `Continuous.matrix_adjugate`); `Ring.inverse` on the
field `ℝ` is `(·)⁻¹` (`Ring.inverse_eq_inv'`), which is measurable
(`measurable_inv`). Entrywise the product of these measurable scalars is
measurable. (Mirrors the entrywise inverse-measurability already used ad hoc in
`RouteMSJIncidenceChart5BigCell.chart5Shift_measurable`, lifted to a generic
reusable form.)
-/

open MeasureTheory Matrix

namespace DLNFibre.Core

/-- **The matrix inverse is measurable (entrywise).** For a matrix built from a
raw pi-type variable `P : Fin n → Fin n → ℝ`, each entry of `(Matrix.of P)⁻¹` is a
measurable function of `P`. Entrywise
`(Matrix.of P)⁻¹ i j = Ring.inverse (det (of P)) * adjugate (of P) i j`
(`Matrix.inv_def`): `det`/`adjugate` are continuous (polynomial in the entries),
`Ring.inverse = (·)⁻¹` on `ℝ` is measurable (`Ring.inverse_eq_inv'` +
`measurable_inv`). The `Matrix.of` wrapper keeps the domain a plain pi type
(which carries `MeasurableSpace`), while the inverse target is real-valued. -/
theorem measurable_matrix_of_inv_apply {n : ℕ} (i j : Fin n) :
    Measurable (fun P : Fin n → Fin n → ℝ => ((Matrix.of P)⁻¹) i j) := by
  have hof : Continuous (Matrix.of : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) :=
    continuous_id
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  have hdet : Measurable (fun P : Fin n → Fin n → ℝ => Ring.inverse (Matrix.of P).det) := by
    rw [Ring.inverse_eq_inv']
    exact measurable_inv.comp (Continuous.matrix_det hof).measurable
  exact hdet.mul ((Continuous.matrix_adjugate hof).matrix_elem i j).measurable

/-! ## Entrywise measurability composition helpers

Matrix-valued functions cannot be stated `Measurable` directly (no
`MeasurableSpace (Matrix …)` instance; see the module note), so measurability of
composite matrix expressions is carried entrywise. These generic helpers let a
matrix product/sum be assembled from the measurability of the factors' entries —
composed to arbitrary depth by feeding one helper's conclusion as the next's
hypothesis. Real-valued throughout, so no `Matrix` measurable-space instance is
touched. -/

/-- **Entrywise measurability of a matrix product.** If every entry of `A x` and
of `B x` is a measurable function of `x`, then so is every entry of `A x * B x`
(`Matrix.mul_apply`: a finite sum of products of measurable scalars). -/
theorem measurable_matrix_mul_entry {X : Type*} [MeasurableSpace X] {p q r : ℕ}
    {A : X → Matrix (Fin p) (Fin q) ℝ} {B : X → Matrix (Fin q) (Fin r) ℝ}
    (hA : ∀ i k, Measurable fun x => A x i k) (hB : ∀ k j, Measurable fun x => B x k j)
    (i : Fin p) (j : Fin r) : Measurable fun x => (A x * B x) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul (hB k j)

/-- **Entrywise measurability of a matrix sum.** `Matrix.add_apply`: the sum's
entry is the sum of the entries. -/
theorem measurable_matrix_add_entry {X : Type*} [MeasurableSpace X] {p q : ℕ}
    {A B : X → Matrix (Fin p) (Fin q) ℝ}
    (hA : ∀ i j, Measurable fun x => A x i j) (hB : ∀ i j, Measurable fun x => B x i j)
    (i : Fin p) (j : Fin q) : Measurable fun x => (A x + B x) i j := by
  simp only [Matrix.add_apply]
  exact (hA i j).add (hB i j)

end DLNFibre.Core
