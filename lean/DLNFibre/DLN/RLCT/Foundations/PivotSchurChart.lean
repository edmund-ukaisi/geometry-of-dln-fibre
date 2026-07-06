import DLNFibre.Core.Matrix.RankNormalForm
import DLNFibre.DLN.RLCT.Foundations.CoreShearMP

/-!
# `DLNFibre.DLN.RLCT.Foundations.PivotSchurChart` — the general-dimension pivot-chart c.o.v. base

The **network-free** base of the general-`L` R1-UPPER boundary peel (design certificate
`expeditions/2026-06-20-aoyagi-full/threads/genm-r1upper-design/design-cert.md`, piece 2). It
supplies the matrix-algebra + measure-theory ingredients the inner fibre bound (`sjBoundaryPeel`, a
LATER tide) needs on each pivot chart of the front factor `A₀ : M₀×M₁`:

* **Aoyagi Lemma 2 — the unit-triangular LDU exposing `Γ`** (§A). On the pivot chart where the `t×t`
  block `P` is invertible, block-form `A₀ = fromBlocks P B C D` factors as `L · diag(P, Γ) · U` with
  `L`, `U` unit-triangular (`det = 1`) and `Γ = D − C P⁻¹ B` the corank block (`aoyagiSchur`). Thin
  wrapper of Mathlib's `fromBlocks_eq_of_invertible₁₁`; the det-1 facts are the "Jacobian 1"
  ALGEBRAIC statement.

* **The pivot-chart cover** (§B). The rank↔minor cover: `t ≤ A.rank ⟺ ∃ row/col `t`-embeddings
  `ρ, κ` with `A.submatrix ρ κ` a unit. The reverse (rank ≥ t ⟹ a nonsingular `t×t` minor exists) is
  the classical direction, built from the banked column-selection `Core.exists_pivot_cols_of_rank`
  plus a row-selection `exists_indep_rows_of_le_rank`; the forward is `rank_submatrix_le`. The
  set-cover form `pivotLocus_eq_iUnion` is what the peel's finite chart cover consumes.

* **The Jacobian-1 change of variables** (§C). The block shear `(x, D) ↦ (x, D − K x)` (the
  `D`-block translation by the pivot-determined correction `K = C P⁻¹ B`) is measure-preserving —
  `measurePreserving_shearSub`, a `skew_product` det-1 fibre translation. This is the MEASURE
  statement of "Jacobian 1"; the concrete Schur correction is measurable
  (`schurCorrection_measurable`). The banked `measurePreserving_coreShear` is pinned as the peel's
  ready tool.

Radial blow-up `Γ = z·V`, the 1-D Beta fibre integral, and the a.e. assembly into `sjBoundaryPeel`
are LATER tides; this module is only the c.o.v. base.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped Matrix

/-! ## §A — Aoyagi Lemma 2: the unit-triangular LDU exposing the Schur block `Γ`

Over a `CommRing`, block index types `m` (pivot), `l` (extra rows), `n` (extra cols). The pivot
block `P : m×m` is invertible; the LDU `fromBlocks P B C D = L · diag(P, Γ) · U` exposes the corank
block `Γ = D − C P⁻¹ B`. This is exactly Aoyagi's Lemma-2 / Theorem-3 reduction, and the
`det L = det U = 1` facts are the algebraic form of the "Jacobian 1" claim. -/

section AoyagiLemma2

variable {m l n : Type*} [Fintype m] [Fintype l] [Fintype n]
  [DecidableEq m] [DecidableEq l] [DecidableEq n]
variable {α : Type*} [CommRing α]

/-- **Aoyagi's Schur complement** `Γ = D − C P⁻¹ B` (pivot `P` invertible), the corank block the
Lemma-2 reduction exposes. -/
def aoyagiSchur (P : Matrix m m α) [Invertible P] (B : Matrix m n α)
    (C : Matrix l m α) (D : Matrix l n α) : Matrix l n α :=
  D - C * ⅟P * B

/-- **The lower unit-triangular factor** `L = [[1, 0], [C P⁻¹, 1]]`. -/
def aoyagiLower (P : Matrix m m α) [Invertible P] (C : Matrix l m α) :
    Matrix (m ⊕ l) (m ⊕ l) α :=
  fromBlocks 1 0 (C * ⅟P) 1

/-- **The upper unit-triangular factor** `U = [[1, P⁻¹ B], [0, 1]]`. -/
def aoyagiUpper (P : Matrix m m α) [Invertible P] (B : Matrix m n α) :
    Matrix (m ⊕ n) (m ⊕ n) α :=
  fromBlocks 1 (⅟P * B) 0 1

/-- **Aoyagi Lemma 2 — the unit-triangular LDU exposing `Γ`.** For invertible pivot `P`,
`fromBlocks P B C D = L · diag(P, Γ) · U`, with `Γ = aoyagiSchur P B C D` the corank block and
`L`, `U` the unit-triangular factors. Direct restatement of `fromBlocks_eq_of_invertible₁₁`. -/
theorem aoyagi_ldu (P : Matrix m m α) [Invertible P] (B : Matrix m n α)
    (C : Matrix l m α) (D : Matrix l n α) :
    fromBlocks P B C D
      = aoyagiLower P C * fromBlocks P 0 0 (aoyagiSchur P B C D) * aoyagiUpper P B :=
  fromBlocks_eq_of_invertible₁₁ P B C D

/-- **The lower factor has determinant 1** (unit lower-triangular; the algebraic "Jacobian 1"). -/
theorem aoyagiLower_det (P : Matrix m m α) [Invertible P] (C : Matrix l m α) :
    (aoyagiLower P C).det = 1 := by
  rw [aoyagiLower, det_fromBlocks_one₁₁]; simp

/-- **The upper factor has determinant 1** (unit upper-triangular; the algebraic "Jacobian 1"). -/
theorem aoyagiUpper_det (P : Matrix m m α) [Invertible P] (B : Matrix m n α) :
    (aoyagiUpper P B).det = 1 := by
  rw [aoyagiUpper, det_fromBlocks_one₁₁]; simp

/-- **The square-block determinant factorisation** `det (fromBlocks P B C D) = det P · det Γ` (needs
`Γ` square, `n = l` — Aoyagi's rectangular `(M₀−t)×(M₁−t)` block is generally NOT square, so this is
the diagnostic square special case). Mathlib's `det_fromBlocks₁₁`, phrased with `aoyagiSchur`. -/
theorem aoyagi_det_square (P : Matrix m m α) [Invertible P] (B : Matrix m l α)
    (C : Matrix l m α) (D : Matrix l l α) :
    (fromBlocks P B C D).det = P.det * (aoyagiSchur P B C D).det := by
  rw [det_fromBlocks₁₁]; rfl

end AoyagiLemma2

/-! ## §B — the pivot-chart cover (rank ↔ nonsingular minor)

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

/-! ## §C — the Jacobian-1 change of variables (measure-preserving block shear)

The MEASURE form of "Jacobian 1": the block shear `(x, D) ↦ (x, D − K x)` — the `D`-block
translation by the pivot-determined correction `K` (concretely `K = C P⁻¹ B`, exposing
`Γ = D − K`) — is measure-preserving. It is a `skew_product` with identity base and per-fibre
translation (volume-invariant). Abstract in `K` measurable; the banked function-space instance is
`measurePreserving_coreShear`, pinned below as the peel's ready tool. -/

section JacobianOne

/-- **The block shear `(x, D) ↦ (x, D − K x)` is measure-preserving** — the MEASURE statement of
"Jacobian 1". A `skew_product`: identity base, per-fibre translation `D ↦ D − K x` (volume-invariant
by `measurePreserving_add_right`). `K : α → β` measurable, `β` an additive group with a
right-invariant volume. The Aoyagi correction `K = C P⁻¹ B` (continuous, hence measurable, on the
pivot chart) plugs in directly to expose `Γ = D − K` as the new fibre variable. -/
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

-- The Aoyagi Lemma-2 LDU (§A) at real block dimensions `t, a, b` — the shape the peel instantiates
-- on the pivot chart (`P` the `t×t` invertible block, `Γ` the `a×b` corank block).
example (t a b : ℕ) (P : Matrix (Fin t) (Fin t) ℝ) [Invertible P]
    (B : Matrix (Fin t) (Fin b) ℝ) (C : Matrix (Fin a) (Fin t) ℝ) (D : Matrix (Fin a) (Fin b) ℝ) :
    fromBlocks P B C D
      = aoyagiLower P C * fromBlocks P 0 0 (aoyagiSchur P B C D) * aoyagiUpper P B :=
  aoyagi_ldu P B C D

end APIPins

end DLNFibre.DLN.RLCT
