/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# `DLNFibre.Core.Matrix.RankMinors` — rank as the vanishing of all larger minors

Over a field, the rank of a matrix is characterised by its minors: `A.rank ≤ r` exactly when every
`(r+1)×(r+1)` submatrix has determinant `0`. This **determinantal-rank criterion**
(`Matrix.rank_le_iff_forall_submatrix_det_eq_zero`) is the classical fact underlying determinantal
loci; it is absent from Mathlib v4.29 (`Mathlib.LinearAlgebra.Matrix.Rank` carries the cardinal-rank
submatrix bound `cRank_submatrix_le` and the unit/full-rank facts, but no minor-vanishing
characterisation of `Matrix.rank`).

The two directions:

* **`→`** (`Matrix.submatrix_det_eq_zero_of_rank_le`): if `A.rank ≤ r`, a square `(r+1)`-submatrix
  has rank `≤ A.rank ≤ r < r+1`, hence is not full rank, hence (`det_eq_zero_of_rank_lt`) has
  `det = 0`. Built on the submatrix rank bound `rank_submatrix_le_rank` (a `ℕ`-rank cast of
  `Matrix.cRank_submatrix_le`).
* **`←`** (`Matrix.exists_submatrix_det_ne_zero_of_le_rank`, contrapositive): if `r+1 ≤ A.rank`,
  extract `r+1` linearly independent rows (`exists_injective_linearIndependent_rows`, from
  `exists_linearIndependent'` + `LinearIndependent.rank_matrix`), then `r+1` independent columns of
  that row-block; the resulting square block has independent columns, hence is a unit
  (`Matrix.linearIndependent_cols_iff_isUnit`), hence has nonzero determinant.

A consequence: `Matrix.rank_map_eq_of_injective` — matrix rank is invariant under the entrywise
application of an injective ring hom between fields, because the criterion is preserved minor by
minor (`Matrix.submatrix_map` + `RingHom.map_det` + `ι` injective ⟹ `ι x = 0 ↔ x = 0`).

These statements live in namespace `Matrix` and mirror the Mathlib home
`Mathlib.LinearAlgebra.Matrix.Rank`, so an upstream move is a file-move with no namespace surgery.
The index maps `er, ec` are *arbitrary* functions `Fin (r+1) → Fin p` / `Fin (r+1) → Fin q` (no
injectivity demanded — a non-injective selection repeats a row or column and the determinant is
`0` regardless, so the criterion is unweakened by allowing them).

**Dependency rule:** pure linear algebra over a field; no DLN dependency. `Core` only — never import
`DLNFibre.DLN`.
-/

namespace Matrix

open Submodule Module

universe u

variable {k : Type u} [Field k]

/-- A square submatrix has rank at most the rank of the full matrix (general index maps over a
field). From `Matrix.cRank_submatrix_le`, cast `Cardinal → ℕ`. -/
theorem rank_submatrix_le_rank {p q : ℕ} (A : Matrix (Fin p) (Fin q) k) {a b : ℕ}
    (f : Fin a → Fin p) (g : Fin b → Fin q) :
    (A.submatrix f g).rank ≤ A.rank := by
  have hc := Matrix.cRank_submatrix_le A f g
  rw [← Matrix.cRank_toNat_eq_rank (A.submatrix f g), ← Matrix.cRank_toNat_eq_rank A]
  exact Cardinal.toNat_le_toNat hc ((A.cRank_le_card_width).trans_lt Cardinal.natCast_lt_aleph0)

/-- A square matrix whose rank is below its size has determinant `0` (over a field): otherwise it
would be a unit of full rank. -/
theorem det_eq_zero_of_rank_lt {p : ℕ} (A : Matrix (Fin p) (Fin p) k) (h : A.rank < p) :
    A.det = 0 := by
  by_contra hdet
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (Ne.isUnit hdet)
  have := Matrix.rank_of_isUnit A hu
  rw [Fintype.card_fin] at this; omega

/-- **Direction `→`** (`rank ≤ r ⟹ minors vanish`). If `A.rank ≤ r` then every `(r+1)×(r+1)`
submatrix of `A` has determinant `0`: the submatrix has rank `≤ A.rank ≤ r < r+1`, so it is not
full rank. -/
theorem submatrix_det_eq_zero_of_rank_le {p q r : ℕ} {A : Matrix (Fin p) (Fin q) k}
    (hr : A.rank ≤ r) (er : Fin (r + 1) → Fin p) (ec : Fin (r + 1) → Fin q) :
    (A.submatrix er ec).det = 0 :=
  det_eq_zero_of_rank_lt _ (lt_of_le_of_lt (rank_submatrix_le_rank A er ec) (by omega))

/-- From `s ≤ A.rank`, an injective row-index family `er : Fin s → Fin p` whose selected rows are
linearly independent. The selected `s × q` submatrix then has full row rank `s`. The engine of the
`←` direction: `exists_linearIndependent'` gives a maximal independent subfamily of the rows, of
cardinality `A.rank`, and `s ≤` that card gives a `Fin s` slice. -/
theorem exists_injective_linearIndependent_rows {p q : ℕ} (A : Matrix (Fin p) (Fin q) k) {s : ℕ}
    (hs : s ≤ A.rank) :
    ∃ er : Fin s → Fin p, Function.Injective er ∧
      LinearIndependent k (fun i ↦ A.row (er i)) := by
  classical
  -- maximal independent subfamily of the rows, indexed by `κ` with an injection `a : κ → Fin p`
  obtain ⟨κ, a, ha_inj, ha_span, ha_li⟩ := exists_linearIndependent' k A.row
  haveI : Module.Finite k (Fin p → k) := inferInstance
  haveI : Finite κ := ha_li.finite
  haveI : Fintype κ := Fintype.ofFinite κ
  -- `Fintype.card κ = A.rank`: independent family spanning the row span of finrank `A.rank`
  have hcard : Fintype.card κ = A.rank := by
    have h1 : finrank k (span k (Set.range (A.row ∘ a))) = Fintype.card κ :=
      finrank_span_eq_card ha_li
    rw [ha_span] at h1
    rw [A.rank_eq_finrank_span_row, ← h1]
  -- choose an injection `Fin s ↪ κ` (since `s ≤ card κ`), compose with `a`
  have hsle : s ≤ Fintype.card κ := by rw [hcard]; exact hs
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le (β := κ) (α := Fin s)
    (by rw [Fintype.card_fin]; exact hsle)
  have hιinj : Function.Injective (ι : Fin s → κ) := Function.Embedding.injective ι
  refine ⟨fun i ↦ a (ι i), ?_, ?_⟩
  · exact fun i j hij ↦ hιinj (ha_inj hij)
  · have hcomp : (fun i ↦ A.row (a (ι i))) = (A.row ∘ a) ∘ (ι : Fin s → κ) := rfl
    rw [hcomp]
    exact ha_li.comp (ι : Fin s → κ) hιinj

/-- **Direction `←`** (`minors vanish ⟹ rank ≤ r`, contrapositive form). If `r + 1 ≤ A.rank` then
some `(r+1)×(r+1)` submatrix has non-zero determinant: extract `r+1` independent rows, then `r+1`
independent columns of that sub-block; the resulting square block has independent columns, hence is
a unit, hence has non-zero determinant. -/
theorem exists_submatrix_det_ne_zero_of_le_rank {p q r : ℕ} (A : Matrix (Fin p) (Fin q) k)
    (hr : r + 1 ≤ A.rank) :
    ∃ (er : Fin (r + 1) → Fin p) (ec : Fin (r + 1) → Fin q),
      Function.Injective er ∧ Function.Injective ec ∧ (A.submatrix er ec).det ≠ 0 := by
  classical
  -- (1) extract `r+1` independent rows of `A`
  obtain ⟨er, her_inj, her_li⟩ := exists_injective_linearIndependent_rows A hr
  set B : Matrix (Fin (r + 1)) (Fin q) k := A.submatrix er id with hB
  -- the rows of `B` are exactly the selected rows, so they are independent and `B.rank = r+1`
  have hBrow : B.row = fun i ↦ A.row (er i) := by
    funext i; rfl
  have hBli : LinearIndependent k B.row := by rw [hBrow]; exact her_li
  have hBrank : B.rank = r + 1 := by
    have := hBli.rank_matrix; rwa [Fintype.card_fin] at this
  -- (2) extract `r+1` independent rows of `Bᵀ` = `r+1` independent columns of `B`
  have hBTrank : (r + 1) ≤ Bᵀ.rank := by rw [Matrix.rank_transpose, hBrank]
  obtain ⟨ec, hec_inj, hec_li⟩ := exists_injective_linearIndependent_rows Bᵀ hBTrank
  -- (3) the square block `C = A.submatrix er ec` has independent columns, hence is a unit
  set C : Matrix (Fin (r + 1)) (Fin (r + 1)) k := A.submatrix er ec with hC
  have hCcol : C.col = fun i ↦ Bᵀ.row (ec i) := by
    funext i j; simp [hC, hB, Matrix.col_apply, Matrix.row_apply, Matrix.transpose_apply,
      Matrix.submatrix_apply]
  have hCli : LinearIndependent k C.col := by rw [hCcol]; exact hec_li
  have hCunit : IsUnit C := Matrix.linearIndependent_cols_iff_isUnit.mp hCli
  refine ⟨er, ec, her_inj, hec_inj, ?_⟩
  exact Matrix.isUnit_iff_isUnit_det C |>.mp hCunit |>.ne_zero

/-- **The determinantal-rank criterion.** Over a field, `A.rank ≤ r` iff every `(r+1)×(r+1)`
submatrix of `A` (selected by *any* index maps `er, ec`) has determinant `0`. The `→` is
`submatrix_det_eq_zero_of_rank_le`; the `←` is the contrapositive via
`exists_submatrix_det_ne_zero_of_le_rank`. Mathlib v4.29 has no packaged version. -/
theorem rank_le_iff_forall_submatrix_det_eq_zero {p q r : ℕ} (A : Matrix (Fin p) (Fin q) k) :
    A.rank ≤ r ↔ ∀ (er : Fin (r + 1) → Fin p) (ec : Fin (r + 1) → Fin q),
      (A.submatrix er ec).det = 0 := by
  constructor
  · exact fun hr er ec ↦ submatrix_det_eq_zero_of_rank_le hr er ec
  · intro hall
    by_contra hlt
    obtain ⟨er, ec, _, _, hne⟩ :=
      exists_submatrix_det_ne_zero_of_le_rank A (Nat.succ_le_of_lt (Nat.not_le.mp hlt))
    exact hne (hall er ec)

/-- **Matrix rank is preserved by an injective ring hom (between fields).** For an injective
`ι : R →+* S` between fields, the entrywise map `B ↦ B.map ι` preserves rank. Proof: via the
determinantal-rank criterion `rank_le_iff_forall_submatrix_det_eq_zero`,
`(B.map ι).rank ≤ r ↔ B.rank ≤ r` for every `r`, because each `(r+1)×(r+1)` minor satisfies
`det ((B.map ι).submatrix er ec) = ι (det (B.submatrix er ec))` (`Matrix.submatrix_map` +
`RingHom.map_det`), and `ι` injective gives `ι x = 0 ↔ x = 0`. The rank base-change micro-lemma the
real↔complex codim transfer rests on.

This is the **entrywise-matrix** base-change-rank variant, distinct from the **linear-map** variant
`finrank_range_baseChange` (`Core.LinearAlgebra.BaseChange`, `K ⊗ f`) and the **flat
differential-family-span** variant `Module.Flat.linearIndependent_one_tmul` (Mathlib, used inline in
`GenericRank`). -/
theorem rank_map_eq_of_injective {R S : Type*} [Field R] [Field S]
    {p q : ℕ} (B : Matrix (Fin p) (Fin q) R) (ι : R →+* S) (hι : Function.Injective ι) :
    (B.map ι).rank = B.rank := by
  have hiff : ∀ r : ℕ, (B.map ι).rank ≤ r ↔ B.rank ≤ r := by
    intro r
    rw [rank_le_iff_forall_submatrix_det_eq_zero (B.map ι),
      rank_le_iff_forall_submatrix_det_eq_zero B]
    refine forall₂_congr (fun er ec ↦ ?_)
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact map_eq_zero_iff ι hι
  exact le_antisymm ((hiff _).2 le_rfl) ((hiff _).1 le_rfl)

end Matrix
