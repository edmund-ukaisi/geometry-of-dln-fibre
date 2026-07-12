import DLNFibre.DLN.RLCT.Validate.RouteMSJDetMono
import DLNFibre.DLN.RLCT.Validate.RouteMSJProductTube

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCorankGram` — the corank-Gram box integral (GAP-B)

**Thread `genm-sj5-schur`, B5-desc GAP-B (the m-column majorant).** The finiteness of the product
corank-Gram box integral `∫∫ det((Y·A)(Y·A)ᵀ)^{−a/2} d(Y,A) < ⊤` (`a < m−b+1`), the majorant target
the cover-seam de-risk (`cover-derisk.md`) identified as the route-agnostic fill of the B5-desc hole.
Consumes the rebuilt PSD determinant monotonicity (`det_le_det_of_posSemidef_sub`, `RouteMSJDetMono`)
and the banked single-matrix square-Wishart endpoint (`detGram_lintegral_lt_top`, `RouteMSJProductTube`).

## What lands here (sorry-free, reusable)

* **`posSemidef_gram_sub_submatrix_cols`** — the **column-drop Loewner bound**: for `A : m×q` and any
  column embedding `ι : Fin m ↪ Fin q`, `A·Aᵀ ≽ A_S·A_Sᵀ` (`A_S = A.submatrix id ι`), i.e.
  `(A·Aᵀ − A_S·A_Sᵀ).PosSemidef`. Quadratic form `xᵀ(A·Aᵀ − A_S·A_Sᵀ)x = ∑_j y_j² − ∑_l y_{ι l}² ≥ 0`
  (`y = Aᵀ·x`; the selected columns are a sub-sum of nonnegatives).
* **`det_gram_le_of_submatrix_cols`** — the **pointwise determinant majorant**: for `Y : b×m`,
  `det((Y·A_S)(Y·A_S)ᵀ) ≤ det((Y·A)(Y·A)ᵀ)`. The column-drop bound, congruence by `Y`
  (`mul_mul_conjTranspose_same`), then PSD det-monotonicity.

## The isolated hole (STOP-worthy — cover-derisk + Codex-confirmed)

* **`corankGram_box_lt_top`** (the ONE `sorry`) — the product corank-Gram finiteness. The pointwise
  det majorant above is built; what remains is genuinely-new analytic content (the a.e. transfer past
  the junk-value at the null rank-deficient locus, and the shrinking-image change of variables to
  `detGram_lintegral_lt_top`) — not clean-standard, so isolated here per the STOP discipline. See its
  docstring for the precise breakdown.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-- Over `ℝ` the conjugate transpose is the transpose (`star = id`). -/
theorem conjTranspose_eq_transpose_real {p r : ℕ} (M : Matrix (Fin p) (Fin r) ℝ) :
    Mᴴ = Mᵀ := by
  ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]

/-- The real Gram quadratic form: `xᵀ(M·Mᵀ)x = ‖Mᵀ·x‖²` (`= (Mᵀx) ⬝ᵥ (Mᵀx)`). -/
theorem gram_quadratic {p r : ℕ} (M : Matrix (Fin p) (Fin r) ℝ) (x : Fin p → ℝ) :
    star x ⬝ᵥ ((M * Mᵀ) *ᵥ x) = (Mᵀ *ᵥ x) ⬝ᵥ (Mᵀ *ᵥ x) := by
  rw [star_trivial, ← mulVec_mulVec, dotProduct_mulVec]
  congr 1
  exact (mulVec_transpose M x).symm

/-- **The column-drop Loewner bound.** For `A : Fin m → Fin q → ℝ` and any column embedding
`ι : Fin m ↪ Fin q`, the Gram matrix decreases (Loewner) when columns are restricted to `ι`:
`A·Aᵀ − A_S·A_Sᵀ` is positive semidefinite, `A_S = A.submatrix id ι`. The quadratic form is
`∑_{j} (Aᵀx)_j² − ∑_{l} (Aᵀx)_{ι l}² ≥ 0` (a sub-sum of nonnegative squares). -/
theorem posSemidef_gram_sub_submatrix_cols {m q : ℕ}
    (A : Matrix (Fin m) (Fin q) ℝ) (ι : Fin m ↪ Fin q) :
    (A * Aᵀ - (A.submatrix id ι) * (A.submatrix id ι)ᵀ).PosSemidef := by
  set AS := A.submatrix id ι with hAS
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Hermitian: difference of two Gram (self-adjoint) matrices
    have h1 : (A * Aᵀ).IsHermitian := by
      have := Matrix.posSemidef_self_mul_conjTranspose A
      rw [conjTranspose_eq_transpose_real] at this; exact this.isHermitian
    have h2 : (AS * ASᵀ).IsHermitian := by
      have := Matrix.posSemidef_self_mul_conjTranspose AS
      rw [conjTranspose_eq_transpose_real] at this; exact this.isHermitian
    exact h1.sub h2
  · intro x
    rw [Matrix.sub_mulVec, dotProduct_sub, gram_quadratic, gram_quadratic]
    -- `ASᵀ *ᵥ x = fun l => (Aᵀ *ᵥ x) (ι l)`
    have hAScol : ASᵀ *ᵥ x = fun l => (Aᵀ *ᵥ x) (ι l) := by
      funext l
      simp only [hAS, mulVec, dotProduct, transpose_apply, submatrix_apply, id_eq]
    rw [hAScol]
    -- `∑ (Aᵀx)_{ι l}² ≤ ∑ (Aᵀx)_j²` (sub-sum of nonneg squares)
    have hsub : (fun l => (Aᵀ *ᵥ x) (ι l)) ⬝ᵥ (fun l => (Aᵀ *ᵥ x) (ι l))
        ≤ (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) := by
      simp only [dotProduct]
      rw [show ∑ l : Fin m, (Aᵀ *ᵥ x) (ι l) * (Aᵀ *ᵥ x) (ι l)
          = ∑ j ∈ Finset.univ.map ι, (Aᵀ *ᵥ x) j * (Aᵀ *ᵥ x) j from
          (Finset.sum_map Finset.univ ι (fun j => (Aᵀ *ᵥ x) j * (Aᵀ *ᵥ x) j)).symm]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => mul_self_nonneg _)
    linarith [hsub]

/-- **The pointwise determinant majorant.** For `Y : Fin b → Fin m → ℝ`, `A : Fin m → Fin q → ℝ`, and
a column embedding `ι : Fin m ↪ Fin q`, the corank-Gram determinant only increases from the restricted
columns: `det ((Y·A_S)(Y·A_S)ᵀ) ≤ det ((Y·A)(Y·A)ᵀ)`, `A_S = A.submatrix id ι`. The column-drop bound
(`posSemidef_gram_sub_submatrix_cols`), congruence by `Y` (`mul_mul_conjTranspose_same`), then PSD
determinant monotonicity (`det_le_det_of_posSemidef_sub`). -/
theorem det_gram_le_of_submatrix_cols {b m q : ℕ}
    (Y : Matrix (Fin b) (Fin m) ℝ) (A : Matrix (Fin m) (Fin q) ℝ) (ι : Fin m ↪ Fin q) :
    ((Y * A.submatrix id ι) * (Y * A.submatrix id ι)ᵀ).det
      ≤ ((Y * A) * (Y * A)ᵀ).det := by
  set AS := A.submatrix id ι with hAS
  -- both Grams as `Y·(·)·Yᵀ`
  have hexp1 : (Y * A) * (Y * A)ᵀ = Y * (A * Aᵀ) * Yᵀ := by
    rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have hexp2 : (Y * AS) * (Y * AS)ᵀ = Y * (AS * ASᵀ) * Yᵀ := by
    rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  rw [hexp1, hexp2]
  -- the difference is `Y·(A·Aᵀ − AS·ASᵀ)·Yᵀ`, PSD by congruence
  have hcong : (Y * (A * Aᵀ) * Yᵀ - Y * (AS * ASᵀ) * Yᵀ).PosSemidef := by
    have hdiff := (posSemidef_gram_sub_submatrix_cols A ι).mul_mul_conjTranspose_same Y
    rw [conjTranspose_eq_transpose_real, ← hAS, Matrix.mul_sub, Matrix.sub_mul] at hdiff
    exact hdiff
  have hPSD2 : (Y * (AS * ASᵀ) * Yᵀ).PosSemidef := by
    have := (Matrix.posSemidef_self_mul_conjTranspose (Y * AS))
    rw [conjTranspose_eq_transpose_real] at this
    rwa [hexp2] at this
  exact det_le_det_of_posSemidef_sub hPSD2 hcong

/-- **The product corank-Gram box integral is finite (the isolated hole — STOP-worthy).** For
`b ≤ m ≤ q` and `a < m − b + 1`, `∫∫ det((Y·A)(Y·A)ᵀ)^{−a/2} d(Y,A) < ⊤`, `Y : b×m`, `A : m×q`
(`Q_b = Y·A`). The majorant target the cover-seam de-risk (`cover-derisk.md §1`) named as the
route-agnostic fill of the B5-desc hole.

The **pointwise** det majorant `det_gram_le_of_submatrix_cols` (with `ι = Fin.castLE`, the first `m`
columns) is BUILT sorry-free above. What remains — the genuinely-new analytic content this `sorry`
isolates (cover-derisk + a decorrelated Codex xhigh consult, `codex/gapb-answer.md`, both STOP):
(i) the majorant transfers to the integrand only A.E. — the junk value `det_small⁻ᵃ = 0` at the null
rank-deficient locus `{det((Y·A_S)(Y·A_S)ᵀ) = 0}` needs an a.e.-positivity (that locus is
Lebesgue-null); (ii) the shrinking-image change of variables `X = Y·A_S` to the banked square-Wishart
`detGram_lintegral_lt_top`, retaining the shrinking image (`|det A_S|⁻ᵇ` cancelled by the image volume
`2^{bm}|det A_S|ᵇ`; do NOT extend to a fixed box — reintroduces `∫|det A_S|^{r−b} = ∞`), which needs a
new quantitative estimate (anisotropic singular-value dependence); (iii) the column-split marginalising
`A`'s last `q−m` columns. NOT clean-standard — isolated per the STOP discipline for a targeted
pen-and-paper cert / focused tide. -/
theorem corankGram_box_lt_top {b m q : ℕ} (hbm : b ≤ m) (hmq : m ≤ q) {a : ℝ}
    (ha : a < (m : ℝ) - b + 1) :
    (∫⁻ p in matBox b m 1 ×ˢ matBox m q 1,
        ENNReal.ofReal (((Matrix.of p.1 * Matrix.of p.2)
          * (Matrix.of p.1 * Matrix.of p.2)ᵀ).det ^ (-a / 2))) < ⊤ := by
  sorry

end DLNFibre.DLN.RLCT
