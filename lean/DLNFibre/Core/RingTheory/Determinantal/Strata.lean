/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Ideal.Maps
import DLNFibre.Core.Matrix.RankMinors
import DLNFibre.Core.RingTheory.Determinantal.Basic

/-!
# `Matrix` — rank strata, the pivot-minor cover, and the ideal ↔ rank-locus connective

Over a field `k`, the matrices `Matrix (Fin p) (Fin q) k` are stratified by rank. This file packages
the two rank loci, the pivot-minor charts that cover the open stratum, and the connective theorem
that ties the closed stratum to the determinantal `(r+1)`-minor ideal of `Basic.lean`.

* **The rank loci.** `rankLeLocus r = {M | M.rank ≤ r}` (the union of all ranks `≤ r`) and
  `rankEqLocus r = {M | M.rank = r}` (the rank-exactly-`r` stratum). The "closed"/"open"-stratum
  reading is geometric motivation — these are bare `Set`s, no topology is proved here.

* **The pivot-minor charts + the cover.** `minorChart s t = {M | the (s,t) minor is invertible}` is
  the principal open cut by the polynomial `detMinorPoly s t`. The keystone existence fact
  `exists_invertible_minor_of_rank` (over a field, a rank-`r` matrix has *some* invertible `r × r`
  minor — absent in Mathlib v4.29) gives the **cover theorem**
  `rankEqLocus_subset_iUnion_minorChart`: the pivot charts cover the rank-exactly-`r` locus.

* **The ideal ↔ rank-locus connective (the new content).** A matrix `M` over the field `k` lies in
  `rankLeLocus r` **iff** the determinantal `(r+1)`-minor ideal
  `Matrix.determinantalIdeal p q k (r+1)` (`Basic.lean`) is killed by evaluation at `M` — i.e. `M`
  is in the **vanishing locus** of that ideal (`rankLeLocus_eq_vanishingLocus`,
  `mem_rankLeLocus_iff_determinantalIdeal_le_ker`). This is the
  three-way identity "rank `≤ r`" ⟺ "all `(r+1)`-minors vanish" ⟺ "in the vanishing locus of
  `determinantalIdeal (r+1)`", at the field/coordinate level (the universal matrix evaluated at the
  `k`-point `M`). It rides on the field-level minor↔rank criterion
  `rank_le_iff_forall_submatrix_det_eq_zero` (`RankMinors`) and the ideal's generator API
  `determinantalIdeal_le_iff` / `eval_detMinorPoly` (`Basic`). It stays at the `k`-point level — the
  scheme-point / residue-field `κ(P)` lift is a separate (P2.d) rung.

**Provenance.** The rank loci + the pivot cover are re-homed verbatim (namespace only) from
`DLNFibre.Core.RankMinorCover`; the minor↔rank criterion lives in `DLNFibre.Core.Matrix.RankMinors`
(namespace `Matrix`, imported here); the determinantal ideal lives in
`DLNFibre.Core.RingTheory.Determinantal.Basic`. All are general matrix/field facts over an arbitrary
field (the ideal over an arbitrary `CommRing`), so they live in the bare `Matrix` namespace,
mirroring the Mathlib home `Mathlib.LinearAlgebra.Matrix.Rank`.

**Dependency rule:** network-free `Core` — never import `DLNFibre.DLN`.
-/

namespace Matrix

open Module

universe u

variable {k : Type u} [Field k] {p q : ℕ}

/-! ## The keystone: a rank-`r` matrix has an invertible `r × r` minor -/

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

/-- **The rank ↔ minor bridge keystone.** Over a field, a matrix `A : Matrix (Fin p)
(Fin q) k` of rank `r` has an invertible `r × r` minor: injective selectors `s : Fin r → Fin p`,
`t : Fin r → Fin q` with `IsUnit ((A.submatrix s t).det)`. The geometric fact under the per-minor
open cover of `rankEqLocus r` — every rank-`r` matrix lies in at least one pivot chart
`minorChart s t`. -/
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

/-! ## The rank loci and the per-minor pivot-chart cover -/

variable (k p q) in
/-- **The per-minor pivot chart** at the pivot position `(s, t)` (`s : Fin r → Fin p` rows,
`t : Fin r → Fin q` columns): the det-open `{M | IsUnit ((M.submatrix s t).det)}` where the `r × r`
minor on rows `s`, columns `t` is invertible. (Principal open in `Mat_{p×q}` cut by the polynomial
`detMinorPoly_{s,t}`.) -/
def minorChart {r : ℕ} (s : Fin r → Fin p) (t : Fin r → Fin q) :
    Set (Matrix (Fin p) (Fin q) k) :=
  {M | IsUnit ((M.submatrix s t).det)}

/-- The rank-exactly-`r` locus (the rank-`= r` stratum) in `Mat_{p×q}` over a field. -/
def rankEqLocus (r : ℕ) : Set (Matrix (Fin p) (Fin q) k) := {M | M.rank = r}

/-- The rank-`≤ r` locus (the union of the strata of rank `≤ r`) in `Mat_{p×q}` over a field. It is
the field-level vanishing locus of the determinantal `(r+1)`-minor ideal
(`rankLeLocus_eq_vanishingLocus`); the "closed"/"open"-stratum language is geometric motivation
only — no topology is proved here (these are bare `Set`s). -/
def rankLeLocus (r : ℕ) : Set (Matrix (Fin p) (Fin q) k) := {M | M.rank ≤ r}

@[simp] theorem mem_rankEqLocus {r : ℕ} {M : Matrix (Fin p) (Fin q) k} :
    M ∈ rankEqLocus (k := k) r ↔ M.rank = r := Iff.rfl

@[simp] theorem mem_rankLeLocus {r : ℕ} {M : Matrix (Fin p) (Fin q) k} :
    M ∈ rankLeLocus (k := k) r ↔ M.rank ≤ r := Iff.rfl

/-- The rank-exactly-`r` locus sits inside the closed rank-`≤ r` locus. -/
theorem rankEqLocus_subset_rankLeLocus (r : ℕ) :
    rankEqLocus (k := k) (p := p) (q := q) r ⊆ rankLeLocus (k := k) r :=
  fun _ hM ↦ le_of_eq hM

/-- **The per-minor opens cover the rank-exactly-`r` locus (the cover theorem).** Every matrix of
rank exactly `r` lies in some pivot chart `minorChart s t` — it has at least one invertible `r × r`
minor (`exists_invertible_minor_of_rank`). So the det-open family `{minorChart s t}` over all
selector pairs `(s, t)` is an open cover of `rankEqLocus r = {M | M.rank = r}` (the non-injective
selectors contribute empty charts — a repeated-index submatrix has det `0`, never a unit — so the
cover is carried by the genuine injective pivot charts). This is the honest geometric content of
"the per-minor charts cover the rank-`= r` stratum" — a genuine cover, not a single chart. -/
theorem rankEqLocus_subset_iUnion_minorChart (r : ℕ) :
    rankEqLocus (k := k) (p := p) (q := q) r
      ⊆ ⋃ (st : (Fin r → Fin p) × (Fin r → Fin q)), minorChart k p q st.1 st.2 := by
  intro M hM
  obtain ⟨s, t, _, _, hdet⟩ := exists_invertible_minor_of_rank M hM
  exact Set.mem_iUnion.mpr ⟨(s, t), hdet⟩

/-- **The cover as an equality.** `rankEqLocus r` is the union of its per-minor charts intersected
with the rank-exactly-`r` condition: `{M | M.rank = r} = ⋃_{(s,t)} ({M.rank = r} ∩ minorChart s t)`.
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

/-! ## The ideal ↔ rank-locus connective

The field-level tie between the closed rank locus and the determinantal `(r+1)`-minor ideal of
`Basic.lean`. A `k`-point `M : Matrix (Fin p) (Fin q) k` is evaluated by the `MvPolynomial` ring hom
`MvPolynomial.eval (fun ij ↦ M ij.1 ij.2)`, sending the coordinate `X (i, j)` to the entry `M i j`;
its kernel is the ideal of polynomials vanishing at `M`. So "`M` is in the vanishing locus of the
ideal `I`" reads as `I ≤ RingHom.ker (eval …)`. -/

/-- **The ideal ↔ rank-locus connective (membership form).** Over a field, a matrix `M` has
`M.rank ≤ r` **iff** the determinantal `(r+1)`-minor ideal `determinantalIdeal p q k (r+1)` lies in
the kernel of evaluation at `M` — i.e. every `(r+1)`-minor polynomial vanishes at `M`. This is the
three-way identity "rank `≤ r`" ⟺ "all `(r+1)`-minors vanish" ⟺ "`M` in the vanishing locus of
`determinantalIdeal (r+1)`", at the field/coordinate level. The proof chains the ideal's generator
criterion `determinantalIdeal_le_iff`, `RingHom.mem_ker`, the evaluation identity
`eval_detMinorPoly`, and the field-level minor↔rank criterion
`rank_le_iff_forall_submatrix_det_eq_zero`. -/
theorem mem_rankLeLocus_iff_determinantalIdeal_le_ker (r : ℕ) (M : Matrix (Fin p) (Fin q) k) :
    M ∈ rankLeLocus (k := k) r
      ↔ determinantalIdeal p q k (r + 1)
          ≤ RingHom.ker (MvPolynomial.eval fun ij ↦ M ij.1 ij.2) := by
  rw [mem_rankLeLocus, rank_le_iff_forall_submatrix_det_eq_zero, determinantalIdeal_le_iff]
  refine forall₂_congr fun s t ↦ ?_
  rw [RingHom.mem_ker, eval_detMinorPoly]

/-- **The ideal ↔ rank-locus connective (set-equality form).** The closed rank-`≤ r` locus `is` the
vanishing locus of the determinantal `(r+1)`-minor ideal: `rankLeLocus r = {M | determinantalIdeal
p q k (r+1) ≤ ker (eval at M)}`. Set-level restatement of
`mem_rankLeLocus_iff_determinantalIdeal_le_ker`. -/
theorem rankLeLocus_eq_vanishingLocus (r : ℕ) :
    rankLeLocus (k := k) (p := p) (q := q) r
      = {M | determinantalIdeal p q k (r + 1)
          ≤ RingHom.ker (MvPolynomial.eval fun ij ↦ M ij.1 ij.2)} :=
  Set.ext fun M ↦ mem_rankLeLocus_iff_determinantalIdeal_le_ker r M

/-! ## Non-vacuity witnesses

The `2 × 2` matrix `!![1,0;0,0]` over `ℚ`: rank `1`, its top-left `1 × 1` minor is the unit `[1]`.
It lies in the per-minor chart at the top-left `1 × 1` pivot, and in the closed locus
`rankLeLocus 1` — so the chart family and the loci are non-vacuous on a genuine instance. -/

/-- **Witness.** `!![1,0;0,0]` lies in the per-minor chart at the top-left `1 × 1` pivot: its
`(0, 0)` minor `[1]` is a unit. -/
example : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ)
    ∈ minorChart ℚ 2 2 (fun _ : Fin 1 ↦ (0 : Fin 2)) (fun _ : Fin 1 ↦ (0 : Fin 2)) := by
  change IsUnit (((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ).submatrix
    (fun _ : Fin 1 ↦ (0 : Fin 2)) (fun _ : Fin 1 ↦ (0 : Fin 2))).det)
  rw [Matrix.det_fin_one, Matrix.submatrix_apply]
  norm_num

end Matrix
