import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import DLNFibre.Core.Matrix.RankNormalForm
import DLNFibre.DLN.RLCT.Foundations.CoreShearMP

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJPivotChart` — the R1-UPPER `(S,J)` peel's c.o.v. base

The **change-of-variables base** for Aoyagi's boundary-0 pivot peel (the residual of `sjBoundaryPeel`,
`RouteMSJResolution.lean`). Self-contained, network-free. The base bundles the four ingredients the
inner fibre bound consumes on each pivot chart of the front factor `A₀ : Matrix m n ℝ`:

* **§A — the unit-triangular change of variables** (`schur_cov`). On a chart where the front factor's
  top-left `t × t` block `A` is invertible, unit-triangular `Q₁` (lower) and `Q₂` (upper) — each of
  determinant `1` (volume-preserving elementary row/column operations, `det_schurLeft`/`det_schurRight`)
  — conjugate the block matrix to block-diagonal form, exposing the **corank block** = the Schur
  complement `Γ = D − C A⁻¹ B`:

      Q₁ · fromBlocks A B C D · Q₂ = fromBlocks A 0 0 Γ,   Γ = D − C · A⁻¹ · B.

  `det_fromBlocks_cov` (`det = det A · det Γ`) is the codimension-count bridge for a square front factor.

* **§B — the reindex → pivot-minor bridge** (`pivotBlock_reindex_eq_submatrix`, `schur_cov_toBlocks`,
  `det_toBlocks_cov`). The top-left block of `A₀.reindex e₀ e₁` is the chosen `(e₀, e₁)`-pivot minor, so
  the chart condition "top-left block invertible" is literally "the chosen `t × t` pivot minor is
  nonsingular"; the abstract `schur_cov` transports through `fromBlocks_toBlocks`.

* **§C — the pivot-chart cover** (`pivotLocus_eq_iUnion`). The rank↔minor cover: over a field,
  `{A | t ≤ A.rank} = ⋃ (ρ, κ) pivotChart ρ κ`, the finite union of the charts on which some `t × t`
  minor of `A` is a unit. The reverse (rank ≥ t ⟹ a nonsingular `t × t` minor) is the classical
  direction, from the banked column selection `Core.exists_pivot_cols_of_rank`; the forward is submatrix
  rank monotonicity (`rank_submatrix_le'`).

* **§D — the Jacobian-`1` (measure) change of variables** (`measurePreserving_shearSub`). The block shear
  `(x, D) ↦ (x, D − K x)` — the `D`-block translation by the pivot-determined correction `K` (concretely
  `K = C A⁻¹ B`, exposing `Γ = D − K`) — is measure-preserving, a `skew_product` det-`1` fibre
  translation. This is the MEASURE form of the `D ↦ Γ` substitution (see the note below).

## The math (§A)

Writing the front factor in blocks `A₀ = [[A, B], [C, D]]` with `A` the invertible `t × t` pivot, the
elementary (unit-triangular, hence `det = 1`) row/column operations

    Q₁ = [[1, 0], [−C A⁻¹, 1]]   (clears the C block: row-reduce),
    Q₂ = [[1, −A⁻¹ B], [0, 1]]   (clears the B block: column-reduce)

give `Q₁ A₀ Q₂ = [[A, 0], [0, D − C A⁻¹ B]]`. The Schur complement `Γ = D − C A⁻¹ B` is the corank block:
its `(M₀ − t) × (M₁ − t)` shape is the codim-charge `(M₀ − t)(M₁ − t)` of the peel (`peelExp`). The
identity is `Matrix.fromBlocks_eq_of_invertible₁₁` (the LDU) read as `Q₁ = L⁻¹`, `Q₂ = U⁻¹`; here it is
re-proved directly by two `fromBlocks_multiply` and the pivot cancellations `⅟A · A = 1`, `A · ⅟A = 1`.

**On "Jacobian `1`" — two distinct facets, both proved here.** (i) The *algebraic* fact
`det Q₁ = det Q₂ = 1` (`det_schurLeft`/`det_schurRight`): the conjugating elementary factors are
volume-preserving. (ii) The *integral / measure* fact that the coordinate substitution
`(A, B, C, D) ↦ (A, B, C, Γ)` — a translation `D ↦ D − C A⁻¹ B` at fixed `(A, B, C)` — is unit-Jacobian:
this is §D `measurePreserving_shearSub` (the abstract block shear `(x, D) ↦ (x, D − K x)`, `K = C A⁻¹ B`).
Facet (ii) was formerly deferred; it now sits in §D. What remains deferred (Scope) is the *use* of these
in the full peel assembly.

## Scope

This is the reachable c.o.v. base — §A–§D above. What USES it (the `sjBoundaryPeel` residual, LATER
tides): the radial blow-up `Γ = z·V` (Jacobian `z^{a−1}`), the 1-D `Beta` fibre integral, and the a.e.
finite-sum assembly over the pivot-chart cover into `sjBoundaryPeel`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped Matrix

section AbstractCov

variable {t a b : Type*} [Fintype t] [Fintype a] [Fintype b]
  [DecidableEq t] [DecidableEq a] [DecidableEq b]

/-- **The unit lower-triangular left factor** `Q₁ = [[1, 0], [−C A⁻¹, 1]]` of the Schur c.o.v.
Clears the lower-left `C` block by a row operation. -/
noncomputable def schurLeft (A : Matrix t t ℝ) (C : Matrix a t ℝ) [Invertible A] :
    Matrix (t ⊕ a) (t ⊕ a) ℝ :=
  fromBlocks 1 0 (-(C * ⅟A)) 1

/-- **The unit upper-triangular right factor** `Q₂ = [[1, −A⁻¹ B], [0, 1]]` of the Schur c.o.v.
Clears the upper-right `B` block by a column operation. -/
noncomputable def schurRight (A : Matrix t t ℝ) (B : Matrix t b ℝ) [Invertible A] :
    Matrix (t ⊕ b) (t ⊕ b) ℝ :=
  fromBlocks 1 (-(⅟A * B)) 0 1

/-- **The Schur complement (corank block)** `Γ = D − C A⁻¹ B`. Its `a × b` shape is the corank
`(M₀ − t) × (M₁ − t)`; the codim-charge `(M₀ − t)(M₁ − t)` is its entry count. -/
noncomputable def schurCompl (A : Matrix t t ℝ) (B : Matrix t b ℝ) (C : Matrix a t ℝ)
    (D : Matrix a b ℝ) [Invertible A] : Matrix a b ℝ :=
  D - C * ⅟A * B

/-- **Aoyagi Lemma 2 — the unit-triangular change of variables.** With the pivot block `A`
invertible, `Q₁ · [[A, B], [C, D]] · Q₂ = [[A, 0], [0, Γ]]`, `Γ = D − C A⁻¹ B` the Schur complement.
Direct block-multiply: `Q₁` clears the `C` block (`⅟A · A = 1`), `Q₂` clears the `B` block
(`A · ⅟A = 1`). -/
theorem schur_cov (A : Matrix t t ℝ) (B : Matrix t b ℝ) (C : Matrix a t ℝ) (D : Matrix a b ℝ)
    [Invertible A] :
    schurLeft A C * fromBlocks A B C D * schurRight A B =
      fromBlocks A 0 0 (schurCompl A B C D) := by
  simp only [schurLeft, schurRight, schurCompl]
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨by simp, by simp, by simp [Matrix.mul_assoc], ?_⟩
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, zero_add,
    Matrix.neg_mul, Matrix.mul_assoc, invOf_mul_self, neg_add_cancel]
  rw [neg_add_eq_sub]

/-- **`det Q₁ = 1` (left factor is volume-preserving).** `Q₁` is unit lower-triangular
(`det = det 1 · det 1`). The algebraic underpinning of the peel's integral Jacobian-`1` (the separate
substitution `D ↦ Γ`, proved as the measure fact `measurePreserving_shearSub` in §D). -/
theorem det_schurLeft (A : Matrix t t ℝ) (C : Matrix a t ℝ) [Invertible A] :
    (schurLeft A C).det = 1 := by
  unfold schurLeft
  rw [det_fromBlocks_zero₁₂, det_one, det_one, mul_one]

/-- **`det Q₂ = 1` (right factor is volume-preserving).** `Q₂` is unit upper-triangular
(`det = det 1 · det 1`). -/
theorem det_schurRight (A : Matrix t t ℝ) (B : Matrix t b ℝ) [Invertible A] :
    (schurRight A B).det = 1 := by
  unfold schurRight
  rw [det_fromBlocks_zero₂₁, det_one, det_one, mul_one]

/-- **The determinant factorises through the corank block** (square front factor) — `det [[A, B],
[C, D]] = det A · det Γ` (`Matrix.det_fromBlocks₁₁`, Schur), `Γ = D − C A⁻¹ B` the corank block. The
codimension-count bridge: with `A` (the pivot) invertible, the full square block matrix is nonsingular
iff the corank block `Γ` is — so the singular locus of the peeled factor is cut out by `Γ`. (The peel's
front factor is rectangular in general; there the corank charge is `Γ`'s entry count `(M₀−t)(M₁−t)`,
`schurCompl`'s `a × b` shape, not a determinant.) -/
theorem det_fromBlocks_cov (A : Matrix t t ℝ) (B : Matrix t a ℝ) (C : Matrix a t ℝ)
    (D : Matrix a a ℝ) [Invertible A] :
    (fromBlocks A B C D).det = A.det * (schurCompl A B C D).det := by
  rw [schurCompl, det_fromBlocks₁₁]

end AbstractCov

/-! ## §B — the reindex → pivot-minor bridge

A **pivot chart** for the front factor `A₀ : Matrix m n ℝ` is a choice of block-splitting equivs
`e₀ : m ≃ t ⊕ a`, `e₁ : n ≃ t ⊕ b` (equivalently: which `t` rows and `t` columns are the pivot) on
which the top-left `t × t` block of the reindexed matrix is invertible — equivalently the chosen
`(e₀, e₁)`-pivot minor `A₀.submatrix (e₀⁻¹∘inl) (e₁⁻¹∘inl)` has nonzero determinant
(`Matrix.invertibleOfIsUnitDet` turns that into the `Invertible` instance). There are finitely many
block-splittings for each `t ≤ min m n`, so these charts form a finite family.

On each chart the abstract `schur_cov` applies verbatim through `fromBlocks_toBlocks`: the front
factor's reindexing is `fromBlocks` of its own blocks, top-left the (invertible) pivot minor. The a.e.
COVERING property (every rank-`≥ t` front factor lies in some chart) is §C `pivotLocus_eq_iUnion`. -/

section PivotChart

/-- **The pivot block is the chosen minor.** The top-left block of the block-split `A₀.reindex e₀ e₁`
is exactly the `(e₀, e₁)`-pivot minor `A₀.submatrix (e₀⁻¹∘inl) (e₁⁻¹∘inl)` — so the chart condition
"top-left block invertible" is literally "the chosen `t × t` pivot minor is nonsingular". -/
theorem pivotBlock_reindex_eq_submatrix {m n t a b : Type*}
    (A₀ : Matrix m n ℝ) (e₀ : m ≃ t ⊕ a) (e₁ : n ≃ t ⊕ b) :
    (A₀.reindex e₀ e₁).toBlocks₁₁
      = A₀.submatrix (fun i => e₀.symm (Sum.inl i)) (fun j => e₁.symm (Sum.inl j)) := by
  ext i j; rfl

variable {t a b : Type*} [Fintype t] [Fintype a] [Fintype b]
  [DecidableEq t] [DecidableEq a] [DecidableEq b]

/-- **The block-indexed change of variables.** For any block-indexed matrix `M'` with invertible
top-left block, `Q₁ · M' · Q₂ = fromBlocks (M'₁₁) 0 0 Γ`. `schur_cov` transported through
`fromBlocks_toBlocks` (`M'` is `fromBlocks` of its own blocks). This is the form the pivot chart uses:
apply it at `M' = A₀.reindex e₀ e₁`. -/
theorem schur_cov_toBlocks (M' : Matrix (t ⊕ a) (t ⊕ b) ℝ) [Invertible M'.toBlocks₁₁] :
    schurLeft M'.toBlocks₁₁ M'.toBlocks₂₁ * M' * schurRight M'.toBlocks₁₁ M'.toBlocks₁₂
      = fromBlocks M'.toBlocks₁₁ 0 0
          (schurCompl M'.toBlocks₁₁ M'.toBlocks₁₂ M'.toBlocks₂₁ M'.toBlocks₂₂) := by
  have h := schur_cov M'.toBlocks₁₁ M'.toBlocks₁₂ M'.toBlocks₂₁ M'.toBlocks₂₂
  rwa [fromBlocks_toBlocks] at h

/-- **The determinant factorises through the corank block (block-indexed, square).** For a square
block-indexed matrix with invertible pivot block, `det M' = det(pivot) · det Γ` — the singular locus of
the peeled factor is cut out by the Schur complement `Γ`. `det_fromBlocks_cov` through
`fromBlocks_toBlocks`. -/
theorem det_toBlocks_cov (M' : Matrix (t ⊕ a) (t ⊕ a) ℝ) [Invertible M'.toBlocks₁₁] :
    M'.det = M'.toBlocks₁₁.det
      * (schurCompl M'.toBlocks₁₁ M'.toBlocks₁₂ M'.toBlocks₂₁ M'.toBlocks₂₂).det := by
  have h := det_fromBlocks_cov M'.toBlocks₁₁ M'.toBlocks₁₂ M'.toBlocks₂₁ M'.toBlocks₂₂
  rwa [fromBlocks_toBlocks] at h

end PivotChart

/-! ## §C — the pivot-chart cover (rank ↔ nonsingular minor)

Over a field `K`, `A : Matrix (Fin m) (Fin n) K`. The cover: `t ≤ A.rank ⟺ ∃ `t`-element row/col
embeddings `ρ, κ` with `A.submatrix ρ κ` a unit. The reverse (rank ≥ t ⟹ a nonsingular `t×t` minor)
is the classical direction — a size-`t` linearly-independent column subfamily
(`exists_indep_cols_of_le_rank`) then the row pivots of that full-column-rank block (the banked
`Core.exists_pivot_cols_of_rank` on the transpose). The forward is submatrix-rank monotonicity. -/

section PivotCover

variable {K : Type*} [Field K] {m n : ℕ}

/-- **Column selection does not increase rank.** The `κ`-selected columns of `A` span a subspace of
the full column span, so `(A.submatrix id κ).rank ≤ A.rank`. -/
theorem rank_submatrix_id_col_le (A : Matrix (Fin m) (Fin n) K) {t : ℕ} (κ : Fin t → Fin n) :
    (A.submatrix (id : Fin m → Fin m) κ).rank ≤ A.rank := by
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro v ⟨j, rfl⟩
  exact ⟨κ j, rfl⟩

/-- **Row selection does not increase rank** (via the column version on the transpose). -/
theorem rank_submatrix_id_row_le (A : Matrix (Fin m) (Fin n) K) {t : ℕ} (ρ : Fin t → Fin m) :
    (A.submatrix ρ (id : Fin n → Fin n)).rank ≤ A.rank := by
  have h : (A.submatrix ρ (id : Fin n → Fin n)).rank
      = (Aᵀ.submatrix (id : Fin n → Fin n) ρ).rank := by
    rw [← Matrix.rank_transpose (A.submatrix ρ (id : Fin n → Fin n)), transpose_submatrix]
  rw [h]
  exact le_trans (rank_submatrix_id_col_le Aᵀ ρ) (le_of_eq (Matrix.rank_transpose A))

/-- **Any `t×t` minor has rank ≤ `A.rank`** (row selection then column selection). -/
theorem rank_submatrix_le' (A : Matrix (Fin m) (Fin n) K) {t : ℕ}
    (ρ : Fin t → Fin m) (κ : Fin t → Fin n) :
    (A.submatrix ρ κ).rank ≤ A.rank := by
  have h : A.submatrix ρ κ
      = (A.submatrix ρ (id : Fin n → Fin n)).submatrix (id : Fin t → Fin t) κ := by
    rw [submatrix_submatrix]; rfl
  rw [h]
  exact le_trans (rank_submatrix_id_col_le (A.submatrix ρ id) κ) (rank_submatrix_id_row_le A ρ)

/-- **`t ≤ A.rank` selects `t` linearly-independent columns.** There is a `t`-element column
embedding `κ` whose column-submatrix `A.submatrix id κ` has rank exactly `t` — the size-`t`
specialisation of the maximal-independent-subfamily argument (`exists_linearIndependent'`) behind
`Core.exists_pivot_cols_of_rank`, taking a `t`-element sub-embedding of the max family. -/
theorem exists_indep_cols_of_le_rank (A : Matrix (Fin m) (Fin n) K) {t : ℕ} (ht : t ≤ A.rank) :
    ∃ κ : Fin t ↪ Fin n,
      (A.submatrix (id : Fin m → Fin m) (κ : Fin t → Fin n)).rank = t := by
  classical
  obtain ⟨ι, a, ha_inj, ha_span, ha_li⟩ := exists_linearIndependent' K A.col
  haveI : Finite ι := ha_li.finite
  haveI : Fintype ι := Fintype.ofFinite ι
  have hrank : Module.finrank K (Submodule.span K (Set.range A.col)) = A.rank :=
    (Matrix.rank_eq_finrank_span_cols A).symm
  have hcard : Fintype.card ι = A.rank := by
    have hfin : Module.finrank K (Submodule.span K (Set.range (A.col ∘ a))) = Fintype.card ι :=
      finrank_span_eq_card ha_li
    rw [ha_span] at hfin
    exact hfin.symm.trans hrank
  -- an embedding `Fin t ↪ ι` since `t ≤ card ι`.
  obtain ⟨g⟩ : Nonempty (Fin t ↪ ι) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin, hcard]; exact ht)
  refine ⟨⟨a ∘ g, ha_inj.comp g.injective⟩, ?_⟩
  set κ₀ : Fin t ↪ Fin n := ⟨a ∘ g, ha_inj.comp g.injective⟩ with hκ₀
  -- the selected columns are independent (restrict the max independent family along `g`).
  have hli : LinearIndependent K
      (A.submatrix (id : Fin m → Fin m) (κ₀ : Fin t → Fin n)).col := by
    have hcol : (A.submatrix (id : Fin m → Fin m) (κ₀ : Fin t → Fin n)).col = (A.col ∘ a) ∘ g := by
      funext j i; rfl
    rw [hcol]
    exact ha_li.comp g g.injective
  rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hli, Fintype.card_fin]

/-- **The pivot-chart cover — reverse direction.** `t ≤ A.rank` yields `t`-element row/col
embeddings `ρ, κ` whose `t×t` minor `A.submatrix ρ κ` is a unit. Select `t` independent columns
(`exists_indep_cols_of_le_rank`); that column block has full column rank, so its transpose has full
row rank and `Core.exists_pivot_cols_of_rank` gives the pivot rows; transpose back to a unit. -/
theorem exists_nonsingular_submatrix_of_le_rank (A : Matrix (Fin m) (Fin n) K) {t : ℕ}
    (ht : t ≤ A.rank) :
    ∃ (ρ : Fin t ↪ Fin m) (κ : Fin t ↪ Fin n), IsUnit (A.submatrix ρ κ) := by
  obtain ⟨κ, hκ⟩ := exists_indep_cols_of_le_rank A ht
  set S := A.submatrix (id : Fin m → Fin m) (κ : Fin t → Fin n) with hS
  have hST : Sᵀ.rank = t := by rw [Matrix.rank_transpose]; exact hκ
  obtain ⟨J, hJ⟩ := DLNFibre.Core.Matrix.exists_pivot_cols_of_rank Sᵀ hST
  -- `hJ : IsUnit (Sᵀ.submatrix id J)`; rewrite through `Sᵀ.submatrix id J = (S.submatrix J id)ᵀ`.
  have heq : Sᵀ.submatrix (id : Fin t → Fin t) (J : Fin t → Fin m)
      = (S.submatrix (J : Fin t → Fin m) (id : Fin t → Fin t))ᵀ :=
    (transpose_submatrix S (J : Fin t → Fin m) (id : Fin t → Fin t)).symm
  rw [heq] at hJ
  have hunit : IsUnit (S.submatrix (J : Fin t → Fin m) (id : Fin t → Fin t)) := by
    rw [Matrix.isUnit_iff_isUnit_det] at hJ ⊢
    rwa [Matrix.det_transpose] at hJ
  refine ⟨J, κ, ?_⟩
  have hSJ : S.submatrix (J : Fin t → Fin m) (id : Fin t → Fin t)
      = A.submatrix (J : Fin t → Fin m) (κ : Fin t → Fin n) := by
    rw [hS, submatrix_submatrix]; rfl
  rwa [hSJ] at hunit

/-- **The pivot-chart cover — forward direction.** A unit `t×t` minor forces `t ≤ A.rank`: the minor
has rank `t` (`rank_of_isUnit`) and every minor's rank is `≤ A.rank` (`rank_submatrix_le'`). -/
theorem isUnit_submatrix_le_rank (A : Matrix (Fin m) (Fin n) K) {t : ℕ}
    (ρ : Fin t ↪ Fin m) (κ : Fin t ↪ Fin n)
    (h : IsUnit (A.submatrix (ρ : Fin t → Fin m) (κ : Fin t → Fin n))) :
    t ≤ A.rank := by
  have h1 : (A.submatrix (ρ : Fin t → Fin m) (κ : Fin t → Fin n)).rank = t := by
    rw [Matrix.rank_of_isUnit _ h, Fintype.card_fin]
  have h2 := rank_submatrix_le' A (ρ : Fin t → Fin m) (κ : Fin t → Fin n)
  omega

/-- **The pivot chart** for a `t`-element row/col embedding pair `(ρ, κ)`: the matrices whose
`t×t` `(ρ,κ)`-minor is a unit — the chart on which Aoyagi's Lemma-2 reduction (§A) is available. -/
def pivotChart {t : ℕ} (ρ : Fin t ↪ Fin m) (κ : Fin t ↪ Fin n) :
    Set (Matrix (Fin m) (Fin n) K) :=
  {A | IsUnit (A.submatrix (ρ : Fin t → Fin m) (κ : Fin t → Fin n))}

/-- **The pivot-chart cover (set form).** The rank-`≥ t` locus is exactly the union of the pivot
charts over all `t`-element row/col embeddings — the finite chart cover the boundary peel consumes
(`⊆` is the load-bearing containment; `⊇` makes it a characterisation). -/
theorem pivotLocus_eq_iUnion (t : ℕ) :
    {A : Matrix (Fin m) (Fin n) K | t ≤ A.rank}
      = ⋃ (ρ : Fin t ↪ Fin m) (κ : Fin t ↪ Fin n), pivotChart ρ κ := by
  ext A
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, pivotChart]
  constructor
  · intro ht
    obtain ⟨ρ, κ, h⟩ := exists_nonsingular_submatrix_of_le_rank A ht
    exact ⟨ρ, κ, h⟩
  · rintro ⟨ρ, κ, h⟩
    exact isUnit_submatrix_le_rank A ρ κ h

end PivotCover

/-! ## §D — the Jacobian-1 change of variables (measure-preserving block shear)

The MEASURE form of "Jacobian `1`": the block shear `(x, D) ↦ (x, D − K x)` — the `D`-block
translation by the pivot-determined correction `K` (concretely `K = C A⁻¹ B`, exposing
`Γ = D − K`) — is measure-preserving. It is a `skew_product` with identity base and per-fibre
translation (volume-invariant). Abstract in `K` measurable; the banked function-space instance is
`measurePreserving_coreShear` (§ API pins), pinned as the peel's ready tool. -/

section JacobianOne

/-- **The block shear `(x, D) ↦ (x, D − K x)` is measure-preserving** — the MEASURE statement of
"Jacobian `1`" (facet (ii) of the module header). A `skew_product`: identity base, per-fibre
translation `D ↦ D − K x` (volume-invariant by `measurePreserving_add_right`). `K : α → β` measurable,
`β` an additive group with a right-invariant volume. The Aoyagi correction `K = C A⁻¹ B` (continuous,
hence measurable, on the pivot chart) plugs in directly to expose `Γ = D − K` as the new fibre
variable. -/
theorem measurePreserving_shearSub {α β : Type*}
    [MeasureSpace α] [MeasureSpace β] [AddGroup β] [MeasurableAdd β] [MeasurableSub₂ β]
    [SFinite (volume : Measure α)] [SFinite (volume : Measure β)]
    [(volume : Measure β).IsAddRightInvariant]
    {K : α → β} (hK : Measurable K) :
    MeasurePreserving (fun p : α × β => (p.1, p.2 - K p.1))
      (volume : Measure (α × β)) (volume : Measure (α × β)) := by
  rw [show (volume : Measure (α × β)) = (volume : Measure α).prod volume from
      Measure.volume_eq_prod _ _]
  exact MeasurePreserving.skew_product (f := id) (g := fun x y => y - K x)
    (MeasurePreserving.id volume)
    (measurable_snd.sub (hK.comp measurable_fst))
    (ae_of_all _ (fun x => by
      change Measure.map (fun y : β => y - K x) volume = volume
      rw [show (fun y : β => y - K x) = (fun y => y + (-K x)) from by funext y; rw [sub_eq_add_neg]]
      exact (measurePreserving_add_right volume (-K x)).map_eq))

end JacobianOne

/-! ## API pins (durable contracts for the LATER radial-blow-up / Beta / assembly tides) -/

section APIPins

-- The banked function-space Jacobian-1 shear the peel wires via `rlctAtOn_comp_homeomorph` /
-- `lintegral` change of variables (the concrete `Fin _ → ℝ` instance of the shear MP).
example (a b c : ℕ) (shift : (Fin a → ℝ) × (Fin c → ℝ) → (Fin b → ℝ)) (hshift : Continuous shift) :
    MeasurePreserving
      (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) =>
        (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2)))
      volume volume :=
  measurePreserving_coreShear a b c shift hshift

-- The Aoyagi Lemma-2 unit-triangular c.o.v. (§A) at real block dimensions `t, a, b` — the shape the
-- peel instantiates on the pivot chart (`A` the `t×t` invertible pivot block, `Γ` the `a×b` corank).
example (t a b : ℕ) (A : Matrix (Fin t) (Fin t) ℝ) [Invertible A]
    (B : Matrix (Fin t) (Fin b) ℝ) (C : Matrix (Fin a) (Fin t) ℝ) (D : Matrix (Fin a) (Fin b) ℝ) :
    schurLeft A C * Matrix.fromBlocks A B C D * schurRight A B
      = Matrix.fromBlocks A 0 0 (schurCompl A B C D) :=
  schur_cov A B C D

-- The pivot-chart cover (§C) at the front-factor row/col types — the peel's residual sums over this
-- finite cover of the rank-`≥ t` locus.
example (m n t : ℕ) :
    {A : Matrix (Fin m) (Fin n) ℝ | t ≤ A.rank}
      = ⋃ (ρ : Fin t ↪ Fin m) (κ : Fin t ↪ Fin n), pivotChart ρ κ :=
  pivotLocus_eq_iUnion t

end APIPins

end DLNFibre.DLN.RLCT
