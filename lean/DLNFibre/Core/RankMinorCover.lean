/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# `DLNFibre.Core.RankMinorCover` — the rank ↔ minor bridge (the cover keystone for B3-2)

The determinantal-rank existence fact, missing in Mathlib v4.29: over a field, a matrix of rank
`r` has **some** invertible `r × r` minor — i.e. there are injective row/column selectors picking
an `r × r` submatrix with unit determinant. This is the geometric fact under the per-minor open
cover of the rank-exactly-`r` locus `Mat^{=r}`: the det-opens `{detMinor_{S,T} ≠ 0}` over the pivot
positions `(S, T)` cover `Mat^{=r}`, because every rank-`r` matrix lies in at least one of them.

**Route (Codex-vetted).** Two symmetric column-extractions, glued by transpose:
1. `rank A = r = finrank (span (cols A))` (`Matrix.rank_eq_finrank_span_cols`). The reusable
   helper `exists_injective_cols_linearIndependent` runs `exists_fun_fin_finrank_span_eq` on
   `Set.range A.col` to pull `r` independent columns by **index** — an injective `t : Fin r → n`
   with `A.col ∘ t` linearly independent.
2. `C := A.submatrix id t` (`p × r`) has full column rank `r` (its columns are `A.col ∘ t`,
   independent). `Cᵀ` is `r × p` of rank `r` (`Matrix.rank_transpose`); a second column-extraction
   on `Cᵀ` gives an injective `s : Fin r → p` with `Cᵀ.col ∘ s = C.row ∘ s` independent. Then
   `D := A.submatrix s t` has `D.row = C.row ∘ s` linearly independent, so
   `Matrix.linearIndependent_rows_iff_isUnit` ⟹ `IsUnit D` ⟹ `IsUnit D.det`
   (`Matrix.isUnit_iff_isUnit_det`).

**Dependency rule:** network-free, `Core`-only (in fact Mathlib-adjacent: a spin-out candidate).
-/

namespace DLNFibre.Core

open Matrix Module

universe u

variable {k : Type u} [Field k] {p q : ℕ}

/-- **Column extraction by index.** Over a field, a matrix `A : Matrix (Fin p) (Fin q) k` of rank
`r` has `r` linearly independent columns *selected by index*: there is an injective
`t : Fin (A.rank) → Fin q` with `A.col ∘ t` linearly independent. (Run
`exists_fun_fin_finrank_span_eq` on `Set.range A.col`, then read off the column indices from
membership in the range.) -/
theorem exists_injective_cols_linearIndependent (A : Matrix (Fin p) (Fin q) k) :
    ∃ t : Fin A.rank → Fin q, Function.Injective t ∧ LinearIndependent k (A.col ∘ t) := by
  classical
  -- rewrite `A.rank` as the col-span finrank so the extracted family's index type matches.
  rw [A.rank_eq_finrank_span_cols]
  obtain ⟨f, hfmem, _hspan, hfli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq k (Set.range A.col)
  -- pick a column index `t i` for each `f i ∈ range A.col`.
  choose t ht using hfmem
  refine ⟨t, ?_, ?_⟩
  · -- `A.col ∘ t = f` is injective, hence `t` is injective.
    have hcomp : A.col ∘ t = f := funext ht
    exact (hcomp ▸ hfli).injective.of_comp
  · -- `A.col ∘ t = f`, which is linearly independent.
    have hcomp : A.col ∘ t = f := funext ht
    rw [hcomp]; exact hfli

/-- **Full-column-rank matrix has an invertible square minor by rows.** A matrix `C : Matrix
(Fin p) (Fin r) k` whose columns are linearly independent (`r ≤ p`, full column rank) has an
invertible `r × r` minor: an injective row selector `s : Fin r → Fin p` with
`IsUnit ((C.submatrix s id)).det`. (Transpose-and-extract: `Cᵀ` is `r × p` of rank `r`; pick `r`
independent columns of `Cᵀ` = rows of `C`.) -/
theorem exists_invertible_square_minor_of_cols_linearIndependent {r : ℕ}
    (C : Matrix (Fin p) (Fin r) k) (hC : LinearIndependent k C.col) :
    ∃ s : Fin r → Fin p, Function.Injective s
      ∧ IsUnit ((C.submatrix s id).det) := by
  classical
  -- `Cᵀ` is `r × p`; its rows are `C.col`, independent, so `rank Cᵀ = r`.
  have hCTrank : Cᵀ.rank = r := by
    have : LinearIndependent k Cᵀ.row := hC
    simpa using this.rank_matrix
  -- pull `r` independent columns of `Cᵀ` (= `r` independent rows of `C`) by index, then
  -- recast the index `Fin Cᵀ.rank` to `Fin r` by precomposing with `finCongr hCTrank`.
  obtain ⟨s₀, hs₀inj, hs₀li⟩ := exists_injective_cols_linearIndependent Cᵀ
  set e : Fin r ≃ Fin Cᵀ.rank := finCongr hCTrank.symm with he
  refine ⟨s₀ ∘ e, hs₀inj.comp e.injective, ?_⟩
  -- the `r × r` minor `C.submatrix (s₀ ∘ e) id` has rows `(Cᵀ.col ∘ s₀) ∘ e`, lin. independent.
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]
  have hrow : (C.submatrix (s₀ ∘ e) id).row = (Cᵀ.col ∘ s₀) ∘ e := by
    funext i
    rw [row_submatrix_eq_comp]
    rfl
  rw [hrow]; exact hs₀li.comp e e.injective

/-- **The rank ↔ minor bridge (B3-2 keystone).** Over a field, a matrix `A : Matrix (Fin p)
(Fin q) k` of rank `r` has an invertible `r × r` minor: injective selectors `s : Fin r → Fin p`,
`t : Fin r → Fin q` with `IsUnit ((A.submatrix s t).det)`. The geometric fact under the per-minor
open cover of `Mat^{=r}` — every rank-`r` matrix lies in at least one det-open `{detMinor ≠ 0}`. -/
theorem exists_invertible_minor_of_rank {r : ℕ} (A : Matrix (Fin p) (Fin q) k) (hr : A.rank = r) :
    ∃ (s : Fin r → Fin p) (t : Fin r → Fin q), Function.Injective s ∧ Function.Injective t
      ∧ IsUnit ((A.submatrix s t).det) := by
  classical
  -- pull `r` independent columns of `A` by index, recast `Fin A.rank → Fin q` to `Fin r → Fin q`.
  obtain ⟨t₀, ht₀inj, ht₀li⟩ := exists_injective_cols_linearIndependent A
  set e : Fin r ≃ Fin A.rank := finCongr hr.symm with he
  set t : Fin r → Fin q := t₀ ∘ e with ht
  have htinj : Function.Injective t := ht₀inj.comp e.injective
  -- `C := A.submatrix id t` is `p × r` with columns `A.col ∘ t`, linearly independent.
  set C : Matrix (Fin p) (Fin r) k := A.submatrix id t with hC
  have hCcol : C.col = A.col ∘ t := by
    funext j; rw [hC, col_submatrix_eq_comp]; rfl
  have hCli : LinearIndependent k C.col := by
    rw [hCcol]; exact ht₀li.comp e e.injective
  -- helper 2 gives an invertible `r × r` minor by a row selector `s`.
  obtain ⟨s, hsinj, hsdet⟩ := exists_invertible_square_minor_of_cols_linearIndependent C hCli
  refine ⟨s, t, hsinj, htinj, ?_⟩
  -- `C.submatrix s id = A.submatrix s t`.
  have hsub : C.submatrix s id = A.submatrix s t := by
    rw [hC, submatrix_submatrix]; rfl
  rwa [hsub] at hsdet

/-! ## The per-minor det-open chart family and the open cover of `Mat^{=r}` -/

variable (k p q) in
/-- **The per-minor pivot chart** at the pivot position `(s, t)` (`s : Fin r → Fin p` rows,
`t : Fin r → Fin q` columns): the det-open `{M | IsUnit ((M.submatrix s t).det)}` where the `r × r`
minor on rows `s`, columns `t` is invertible. (Principal open in `Mat_{p×q}` cut by the polynomial
`detMinor_{s,t}`; the top-left case is `DeterminantalChart.pivotRankChart`'s `IsUnit Δ.det`
condition, with `s, t` the inclusions of the first `r` indices.) -/
def minorChart {r : ℕ} (s : Fin r → Fin p) (t : Fin r → Fin q) :
    Set (Matrix (Fin p) (Fin q) k) :=
  {M | IsUnit ((M.submatrix s t).det)}

/-- The rank-exactly-`r` locus in `Mat_{p×q}` over a field. -/
def rankEqLocus (r : ℕ) : Set (Matrix (Fin p) (Fin q) k) := {M | M.rank = r}

/-- **The per-minor opens cover the rank-exactly-`r` locus (B3-2 headline).** Every matrix of rank
exactly `r` lies in some pivot chart `minorChart s t` — it has at least one invertible `r × r`
minor (`exists_invertible_minor_of_rank`). So the det-open family `{minorChart s t}` over the pivot
positions `(s, t)` is an open cover of `Mat^{=r} = {M | M.rank = r}`. This is the honest geometric
content of "the per-minor charts cover `Mat^{=r}`" — a genuine cover, not a single chart. -/
theorem rankEqLocus_subset_iUnion_minorChart (r : ℕ) :
    rankEqLocus (k := k) (p := p) (q := q) r
      ⊆ ⋃ (st : (Fin r → Fin p) × (Fin r → Fin q)), minorChart k p q st.1 st.2 := by
  intro M hM
  obtain ⟨s, t, _, _, hdet⟩ := exists_invertible_minor_of_rank M hM
  exact Set.mem_iUnion.mpr ⟨(s, t), hdet⟩

/-- **The cover as an equality.** `Mat^{=r}` is the union of its per-minor charts intersected with
the rank-exactly-`r` condition: `{M | M.rank = r} = ⋃_{(s,t)} ({M.rank = r} ∩ minorChart s t)`.
(The `⊆` is `rankEqLocus_subset_iUnion_minorChart`; the `⊇` is immediate since each piece carries
the rank condition.) -/
theorem rankEqLocus_eq_iUnion_inter_minorChart (r : ℕ) :
    rankEqLocus (k := k) (p := p) (q := q) r
      = ⋃ (st : (Fin r → Fin p) × (Fin r → Fin q)),
          (rankEqLocus r ∩ minorChart k p q st.1 st.2) := by
  apply Set.Subset.antisymm
  · intro M hM
    obtain ⟨s, t, _, _, hdet⟩ := exists_invertible_minor_of_rank M hM
    exact Set.mem_iUnion.mpr ⟨(s, t), hM, hdet⟩
  · exact Set.iUnion_subset fun _ ↦ Set.inter_subset_left

/-! ## Non-vacuity witness — a concrete matrix lies in a per-minor chart

The `2 × 2` matrix `!![1,0;0,0]` over `ℚ`: its top-left `1 × 1` minor is the unit `[1]`, so it lies
in the per-minor chart at the top-left pivot `(s, t) = (0, 0)` — the chart family is non-vacuous on
a genuine instance. -/

/-- **Witness.** `!![1,0;0,0]` lies in the per-minor chart at the top-left `1 × 1` pivot: its
`(0, 0)` minor `[1]` is a unit. -/
example : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ)
    ∈ minorChart ℚ 2 2 (fun _ : Fin 1 ↦ (0 : Fin 2)) (fun _ : Fin 1 ↦ (0 : Fin 2)) := by
  show IsUnit (((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ).submatrix
    (fun _ : Fin 1 ↦ (0 : Fin 2)) (fun _ : Fin 1 ↦ (0 : Fin 2))).det)
  rw [Matrix.det_fin_one, Matrix.submatrix_apply]
  norm_num

end DLNFibre.Core
