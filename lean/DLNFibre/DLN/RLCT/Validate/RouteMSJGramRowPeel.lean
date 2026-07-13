import DLNFibre.DLN.RLCT.Validate.RouteMSJBorderedGram

/-!
# `RouteMSJGramRowPeel` — the product-of-Schur-residuals factorisation of the Gram determinant

**Thread `genm-sj5-domination`, T-Obl3b mountain, build tile #3 piece (ii).** Iterating the
bordered-Gram / Schur-complement recursion `borderedGram_det` (`RouteMSJBorderedGram`) over all rows
of a linearly independent family gives the full product factorisation

    (gram ℝ v).det = ∏ᵢ (Schur residual of `v i` against `v 0, …, v (i-1)`),

the re-formulation cert §6 form `det(Q Qᵀ) = ∏ᵢ ‖qᵢ^⊥‖²`.

This module is **abstract and Mathlib-only** (inner-product-space level). The concrete `Q Qᵀ` and
measure-theoretic content is already banked in `RouteMSJProductTube`: the row-tuple identification
`rowsEquiv`, the Gram identity `gram_rowsEquiv : gram ℝ (rowsEquiv X) = X Xᵀ`, and the Haar CoV
`measurePreserving_rowsEquiv`. The concrete `det(X Xᵀ) = ∏ …` form is a two-line corollary there
(consume `gram_rowsEquiv` + `gramDet_eq_prod`), living in the DLN closure alongside the CoV.

## What lands here (sorry-free)

* **`gramSchurSeq`** — the Schur residual of `v i` against the earlier vectors: the Schur complement
  scalar of the length-`(i+1)` prefix of `v`, peeling its last entry `v i`.
* **`gramDet_eq_prod`** — for a linearly independent family, `(gram ℝ v).det = ∏ᵢ gramSchurSeq v i`.
  The iterated bordered-Gram recursion.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Schur residual of `v i` against the earlier vectors `v 0, …, v (i-1)`: the Schur complement
scalar of the length-`(i+1)` prefix of `v`, peeling its last entry `v i`. -/
noncomputable def gramSchurSeq {n : ℕ} (v : Fin n → E) (i : Fin n) : ℝ :=
  borderedGramSchur (v ∘ Fin.castLE (Nat.succ_le_of_lt i.isLt))

private lemma gramSchurSeq_last {n : ℕ} (v : Fin (n + 1) → E) :
    gramSchurSeq v (Fin.last n) = borderedGramSchur v := rfl

private lemma gramSchurSeq_castSucc {n : ℕ} (v : Fin (n + 1) → E) (i : Fin n) :
    gramSchurSeq v i.castSucc = gramSchurSeq (v ∘ Fin.castSucc) i := rfl

/-- **The product-of-Schur-residuals factorisation** of the Gram determinant: for a linearly
independent family, `(gram ℝ v).det = ∏ᵢ (Schur residual of `v i` against the earlier vectors)`.
This is the iterated bordered-Gram recursion — the product form `det(Q Qᵀ) = ∏ᵢ ‖qᵢ^⊥‖²`. -/
theorem gramDet_eq_prod {n : ℕ} (v : Fin n → E) (hli : LinearIndependent ℝ v) :
    (gram ℝ v).det = ∏ i : Fin n, gramSchurSeq v i := by
  induction n with
  | zero => simp [Matrix.det_fin_zero]
  | succ n ih =>
      have hli' : LinearIndependent ℝ (v ∘ Fin.castSucc) :=
        hli.comp Fin.castSucc (Fin.castSucc_injective n)
      rw [borderedGram_det v hli', Fin.prod_univ_castSucc, gramSchurSeq_last]
      congr 1
      rw [ih (v ∘ Fin.castSucc) hli']
      exact Finset.prod_congr rfl fun i _ => (gramSchurSeq_castSucc v i).symm

end DLNFibre.DLN.RLCT
