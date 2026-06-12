import DLNFibre.Core.Submult
import DLNFibre.Core.RankPattern
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# `DLNFibre.Core.IntervalModule` — interval modules, direct sums, and their rank patterns (rung 4b)

The interval (lace) modules `M_{ij}` of the type-A Gabriel decomposition (Le Halleur–Rimányi 2024,
Thm 2.5) realised on the concrete `Setup.Tuple` encoding, with their matrix-side rank patterns.

* `intervalDim i j k = if i ≤ k ∧ k ≤ j then 1 else 0` — the dimension vector `e_{ij}` of `M_{ij}`
  (each vertex in `[i,j]` is `1`-dimensional, else `0`).
* `intervalModule i j : Tuple (intervalDim i j)` — the chain `k` on `[i,j]` with identity maps: the
  edge at `t` is the `1×1` identity exactly when both endpoints lie in `[i,j]` (the edge is
  *active*), else the (dimension-forced) zero block.
* `rankPattern_intervalModule` — the **indicator**: `rankPattern (M_{ij}) i' j' = 1` iff
  `[i',j'] ⊆ [i,j]` (`i ≤ i' ∧ j' ≤ j`), else `0`. This is the single-summand half of Prop 3.1b;
  equivalently `submult (M_{ij}) i' j'` is the `1×1` identity when `[i',j'] ⊆ [i,j]` and a
  zero-dimensional block otherwise.
* `dirSum A B : Tuple (fun k ↦ d k + d' k)` — the binary direct sum, block-diagonal
  `(A ⊕ B)_t = fromBlocks A_t 0 0 B_t` (modulo the `Fin (a+b) ≃ Fin a ⊕ Fin b` reindex), with
  `rankPattern_dirSum` the block-rank additivity
  `rankPattern (A ⊕ B) = rankPattern A + rankPattern B` (over a `Field`).
* `intervalDirectSum L` — the finite direct sum `⊕_{(a,b) ∈ L} M_{ab}` over a list of interval
  endpoints (multiplicities = list multiplicities), with **headline**
  `rankPattern_intervalDirectSum_eq_cumul : rankPattern (⊕ M^m) i j = cumul N m̄ i j` (`m̄` the
  list's multiplicity array), folding the indicator and block-additivity into the
  `RankPattern.cumul` inversion engine — the full interval-module side of Prop 3.1b.

**Scope.** This is the *interval-module / direct-sum* side only. The statement that the rank
pattern of an **arbitrary** tuple equals `cumul` of its Gabriel multiplicities (Prop 3.1b, the
*completeness* direction) needs the barcode-basis existence theorem (rung 4d) and is **not** claimed
here: we only show that the *constructed* interval direct sum has rank pattern `cumul m̄`.

**Typeclass.** `CommRing k` carries the definitions and the block matrices; `Nontrivial k` is needed
wherever a rank of `1` appears (it is `Matrix.rank_one`). **Dependency rule:** never import
`DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix

universe u

variable {k : Type u} [CommRing k] {N : ℕ}

/-! ## The interval module `M_{ij}` -/

/-- The dimension vector `e_{ij}` of the interval module `M_{ij}`: `1` on `[i,j]`, else `0`. -/
def intervalDim (i j : Fin (N + 1)) (l : Fin (N + 1)) : ℕ := if i ≤ l ∧ l ≤ j then 1 else 0

/-- The edge at `t` of `M_{ij}` is **active** when both its endpoints lie in `[i,j]`,
`i ≤ t ∧ t+1 ≤ j` — equivalently `intervalDim` is `1` at both `t.castSucc` and `t.succ`. -/
def intervalActive (i j : Fin (N + 1)) (t : Fin N) : Prop := i ≤ t.castSucc ∧ t.succ ≤ j

instance (i j : Fin (N + 1)) (t : Fin N) : Decidable (intervalActive i j t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The interval module `M_{ij} : Tuple (intervalDim i j)`: the edge map at `t` is the constant-`1`
matrix when the edge is active (the `1×1` identity, both endpoints in `[i,j]`), else `0`. The
constant-`1` form typechecks at every `t` (the matrix is `0`-dimensional off the interval) and is
the genuine `1×1` identity on the active edges (`intervalModule_active_eq_one`). -/
def intervalModule (i j : Fin (N + 1)) : Tuple (k := k) (intervalDim i j) :=
  fun t _ _ ↦ if intervalActive i j t then (1 : k) else 0

/-- `e_{ij}` is `1` inside the interval. -/
theorem intervalDim_eq_one {i j l : Fin (N + 1)} (h : i ≤ l ∧ l ≤ j) : intervalDim i j l = 1 := by
  rw [intervalDim, if_pos h]

/-- `e_{ij}` is `0` outside the interval. -/
theorem intervalDim_eq_zero {i j l : Fin (N + 1)} (h : ¬ (i ≤ l ∧ l ≤ j)) :
    intervalDim i j l = 0 := by
  rw [intervalDim, if_neg h]

/-- On an **active** edge `t` (`i ≤ t ∧ t+1 ≤ j`) the edge map of `M_{ij}` is the `1×1` identity:
both endpoint dimensions are `1`, so the constant-`1` matrix is `(1 : Matrix (Fin 1) (Fin 1) k)`
once the dimensions are rewritten. -/
theorem intervalModule_active_eq_one (i j : Fin (N + 1)) (t : Fin N) (ht : intervalActive i j t) :
    intervalModule (k := k) i j t = fun _ _ ↦ (1 : k) := by
  funext a b; rw [intervalModule, if_pos ht]

/-! ## The single-module indicator rank pattern -/

/-- The constant-`1` matrix over single-element index types has rank `1` (`k` nontrivial): it is the
`1×1` identity up to reindexing to `Fin 1`. -/
theorem rank_const_one {m n : Type*} [Fintype n] [Unique m] [Unique n] [Nontrivial k] :
    Matrix.rank (Matrix.of (fun _ _ ↦ (1 : k)) : Matrix m n k) = 1 := by
  let M : Matrix m n k := Matrix.of (fun _ _ ↦ (1 : k))
  let em : m ≃ Fin 1 := Equiv.ofUnique m (Fin 1)
  let en : n ≃ Fin 1 := Equiv.ofUnique n (Fin 1)
  have hreidx : Matrix.reindex em en M = (1 : Matrix (Fin 1) (Fin 1) k) := by
    funext a b
    simp only [M, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Matrix.one_apply,
      if_pos (Subsingleton.elim a b)]
  calc Matrix.rank M
      = Matrix.rank (Matrix.reindex em en M) := (Matrix.rank_reindex em en M).symm
    _ = Matrix.rank (1 : Matrix (Fin 1) (Fin 1) k) := by rw [hreidx]
    _ = 1 := by rw [Matrix.rank_one, Fintype.card_fin]

/-- The diagonal sub-product `submult (M_{ij}) i' i'` is the constant-`1` matrix when `i' ∈ [i,j]`
(its single dimension is `1`). The identity `1` written as the constant-`1` matrix on `Fin 1`. -/
theorem submult_intervalModule_self {i j i' : Fin (N + 1)} (hi : i ≤ i') (hj : i' ≤ j) :
    submult (intervalDim i j) (intervalModule (k := k) i j) i' i' le_rfl = fun _ _ ↦ (1 : k) := by
  rw [submult_self]
  funext a b
  have : Subsingleton (Fin (intervalDim i j i')) := by
    rw [intervalDim_eq_one ⟨hi, hj⟩]; infer_instance
  simp only [Matrix.one_apply, if_pos (Subsingleton.elim a b)]

/-- **Sub-product on a contained interval.** When `[i',j'] ⊆ [i,j]` (so `i ≤ i'` and `j' ≤ j`), the
interval sub-product `submult (M_{ij}) i' j'` is the constant-`1` matrix — the `1×1` identity (both
endpoint dimensions, and every middle dimension, are `1`). Proved by induction on the upper index
through `submult_succ`, using `intervalModule_active_eq_one` on each (active) edge. -/
theorem submult_intervalModule_subset (i j : Fin (N + 1)) {i' j' : Fin (N + 1)} (hij : i' ≤ j')
    (hi : i ≤ i') (hj : j' ≤ j) :
    submult (intervalDim i j) (intervalModule (k := k) i j) i' j' hij = fun _ _ ↦ (1 : k) := by
  induction j' using Fin.induction with
  | zero =>
    obtain rfl : i' = 0 := Fin.le_zero_iff.mp hij
    exact submult_intervalModule_self hi hj
  | succ p ih =>
    rcases eq_or_lt_of_le hij with heq | hlt
    · obtain rfl := heq
      exact submult_intervalModule_self hi hj
    · -- `i' ≤ p.castSucc`, so peel the top (active) edge `p`
      have hip : i' ≤ p.castSucc := by
        rw [Fin.le_castSucc_iff]; exact hlt
      have hpj : p.castSucc ≤ j := le_trans (Fin.castSucc_le_succ p) hj
      rw [submult_succ (intervalDim i j) (intervalModule i j) i' p hip, ih hip hpj]
      have hact : intervalActive i j p := ⟨le_trans hi hip, hj⟩
      rw [intervalModule_active_eq_one i j p hact]
      -- `(const 1) * (const 1)` over a `Fin 1` middle index is `const 1`
      funext a b
      have hsub : Subsingleton (Fin (intervalDim i j p.castSucc)) := by
        rw [intervalDim_eq_one ⟨le_trans hi hip, hpj⟩]; infer_instance
      have : Fintype.card (Fin (intervalDim i j p.castSucc)) = 1 := by
        rw [intervalDim_eq_one ⟨le_trans hi hip, hpj⟩]; rfl
      simp only [Matrix.mul_apply]
      rw [Finset.sum_congr rfl (fun x _ ↦ by ring : ∀ x ∈ _, (1 : k) * 1 = 1)]
      rw [Finset.sum_const, Finset.card_univ, this, one_smul]

/-- A matrix whose **column** index is empty has rank `0` (its `mulVecLin` has trivial domain, so
the range is `⊥`). Needs `Nontrivial k` (over a trivial ring `finrank ⊥ = 1`). -/
theorem rank_eq_zero_of_isEmpty_cols [Nontrivial k] {m n : Type*} [Fintype n]
    [IsEmpty n] (A : Matrix m n k) : A.rank = 0 := by
  rw [Matrix.rank]
  have hbot : LinearMap.range A.mulVecLin = ⊥ := by
    rw [LinearMap.range_eq_bot]
    refine LinearMap.ext fun v ↦ ?_
    have : Subsingleton (n → k) := inferInstance
    rw [Subsingleton.elim v 0, map_zero, LinearMap.zero_apply]
  rw [hbot]; exact finrank_bot k (m → k)

/-- A matrix whose **row** index is empty has rank `0` (its `mulVecLin` has trivial codomain, so the
range is a subsingleton). Needs `Nontrivial k`. -/
theorem rank_eq_zero_of_isEmpty_rows [Nontrivial k] {m n : Type*} [Fintype n]
    [IsEmpty m] (A : Matrix m n k) : A.rank = 0 := by
  rw [Matrix.rank]
  have : Subsingleton (m → k) := inferInstance
  exact Module.finrank_zero_of_subsingleton (R := k) (M := LinearMap.range A.mulVecLin)

/-- **The single-module indicator (Prop 3.1b, summand half).** The rank pattern of the interval
module `M_{ij}` is the indicator of containment: `r_{i'j'}(M_{ij}) = 1` exactly when
`[i',j'] ⊆ [i,j]` (`i ≤ i' ∧ j' ≤ j`), else `0`. Equivalently `submult (M_{ij}) i' j'` is the
`1×1` identity when `[i',j'] ⊆ [i,j]` and a zero-dimensional block otherwise. -/
theorem rankPattern_intervalModule [Nontrivial k] (i j : Fin (N + 1)) {i' j' : Fin (N + 1)}
    (hij : i' ≤ j') :
    rankPattern (intervalDim i j) (intervalModule (k := k) i j) i' j' hij
      = if i ≤ i' ∧ j' ≤ j then 1 else 0 := by
  rw [rankPattern]
  by_cases h : i ≤ i' ∧ j' ≤ j
  · -- containment: the sub-product is the `1×1` identity, rank `1`
    rw [if_pos h]
    have hsub := submult_intervalModule_subset (k := k) i j hij h.1 h.2
    have hi1 : intervalDim i j i' = 1 := intervalDim_eq_one ⟨h.1, le_trans hij h.2⟩
    have hj1 : intervalDim i j j' = 1 := intervalDim_eq_one ⟨le_trans h.1 hij, h.2⟩
    have : Unique (Fin (intervalDim i j i')) := by rw [hi1]; infer_instance
    have : Unique (Fin (intervalDim i j j')) := by rw [hj1]; infer_instance
    rw [hsub]; exact rank_const_one
  · -- non-containment: a boundary dimension is `0`, so the block is rank `0`
    rw [if_neg h]
    rw [not_and_or] at h
    rcases h with hi | hj
    · -- `¬ i ≤ i'`, so `i'` is below the interval: `intervalDim i j i' = 0`, empty columns
      have h0 : intervalDim i j i' = 0 := intervalDim_eq_zero (by tauto)
      have : IsEmpty (Fin (intervalDim i j i')) := by rw [h0]; infer_instance
      exact rank_eq_zero_of_isEmpty_cols _
    · -- `¬ j' ≤ j`, so `j'` is above the interval: `intervalDim i j j' = 0`, empty rows
      have h0 : intervalDim i j j' = 0 := intervalDim_eq_zero (by tauto)
      have : IsEmpty (Fin (intervalDim i j j')) := by rw [h0]; infer_instance
      exact rank_eq_zero_of_isEmpty_rows _

/-! ## The indicator is `cumul` of a single Kostant delta

Ties the single-module rank pattern to the inversion engine `RankPattern.cumul`: the indicator
`r_{i'j'}(M_{ij})` is exactly `cumul N` of the array with a single `1` at `(i,j)` — the
`m = δ_{(i,j)}` case of Prop 3.1b. -/

/-- The single-entry Kostant array `δ_{(i,j)}` over `ℤ`: `1` at `(i,j)`, else `0`. -/
def singleDelta (i j : Fin (N + 1)) : ℤ → ℤ → ℤ :=
  fun a b ↦ if a = (i : ℤ) ∧ b = (j : ℤ) then 1 else 0

/-- **The indicator is `cumul` of the single delta.** `rankPattern (M_{ij}) i' j'` equals
`cumul N δ_{(i,j)}` evaluated at `(i',j')` — the single-summand instance of Prop 3.1b, `r = cumul m`
for `m = δ_{(i,j)}`. -/
theorem rankPattern_intervalModule_eq_cumul [Nontrivial k] (i j : Fin (N + 1))
    {i' j' : Fin (N + 1)} (hij : i' ≤ j') :
    (rankPattern (intervalDim i j) (intervalModule (k := k) i j) i' j' hij : ℤ)
      = cumul (N : ℤ) (singleDelta i j) (i' : ℤ) (j' : ℤ) := by
  rw [rankPattern_intervalModule, cumul_apply, apply_ite (Nat.cast : ℕ → ℤ), Nat.cast_one,
    Nat.cast_zero]
  simp only [singleDelta]
  -- the box double sum of a single delta is `1` iff `(i,j)` lies in `[0,i'] × [j',N]`
  rw [Finset.sum_comm]
  by_cases h : i ≤ i' ∧ j' ≤ j
  · rw [if_pos h]
    rw [Finset.sum_eq_single (j : ℤ), Finset.sum_eq_single (i : ℤ)]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro a _ ha; rw [if_neg (by tauto)]
    · intro hbad; exact absurd (Finset.mem_Icc.mpr ⟨by positivity, by
        exact_mod_cast Fin.le_iff_val_le_val.mp h.1⟩) hbad
    · intro b _ hb; exact Finset.sum_eq_zero fun a _ ↦ if_neg (by tauto)
    · intro hbad; refine absurd (Finset.mem_Icc.mpr ⟨by exact_mod_cast Fin.le_iff_val_le_val.mp h.2,
        by exact_mod_cast Nat.lt_succ_iff.mp j.isLt⟩) hbad
  · rw [if_neg h]
    rw [not_and_or] at h
    symm
    apply Finset.sum_eq_zero
    intro b hb
    apply Finset.sum_eq_zero
    intro a ha
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    rw [Finset.mem_Icc] at ha hb
    rcases h with hi | hj
    · exact hi (Fin.le_iff_val_le_val.mpr (by exact_mod_cast ha.2))
    · exact hj (Fin.le_iff_val_le_val.mpr (by exact_mod_cast hb.1))

/-! ## Block-diagonal rank additivity

The Mathlib-level lever for direct sums: the rank of a block-diagonal matrix `fromBlocks A 0 0 B`
is `rank A + rank B`. There is **no** off-the-shelf `Matrix.rank_fromBlocks` at this pin, so it is
proved here through the `mulVecLin`/`prodMap` correspondence and `Module.finrank_prod`. This is the
one step that genuinely needs a **field** (so the range subspaces are free and finite-dimensional);
the rest of the file is `CommRing`. -/

/-- The product submodule `p.prod q : Submodule R (M × M')` is linearly equivalent to `p × q`
(it is `p × q` carved out of `M × M'`). -/
noncomputable def submoduleProdEquiv {R M M' : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
    (p : Submodule R M) (q : Submodule R M') : (p.prod q) ≃ₗ[R] p × q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1, y.2), by constructor <;> simp⟩
  left_inv x := by ext <;> rfl
  right_inv x := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_smul' r x := by ext <;> rfl

/-- `finrank` is additive on a product submodule (finite-dimensional ambients). -/
theorem finrank_submodule_prod {K M M' : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module K M']
    [FiniteDimensional K M] [FiniteDimensional K M']
    (p : Submodule K M) (q : Submodule K M') :
    Module.finrank K (p.prod q) = Module.finrank K p + Module.finrank K q := by
  rw [(submoduleProdEquiv p q).finrank_eq, Module.finrank_prod]

/-- **Block-diagonal rank additivity.** `rank (fromBlocks A 0 0 B) = rank A + rank B` over a field
(the column space of the block-diagonal matrix is the direct sum of the two column spaces). The
matrix-side lever for direct sums. -/
theorem rank_fromBlocks_zero_zero {K : Type*} [Field K] {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin b) K) (B : Matrix (Fin c) (Fin d) K) :
    (Matrix.fromBlocks A 0 0 B).rank = A.rank + B.rank := by
  classical
  let Er := LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin c) K K
  let Ec := LinearEquiv.sumArrowLequivProdArrow (Fin b) (Fin d) K K
  let f := (Matrix.fromBlocks A 0 0 B).mulVecLin
  let g := A.mulVecLin.prodMap B.mulVecLin
  -- the block-diagonal map is `g` conjugated by the `Sum ≃ Prod` reindexings of the function spaces
  have hfg : Er.toLinearMap.comp f = g.comp Ec.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · ext i
      simp only [f, g, Er, Ec, LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
        Matrix.fromBlocks_mulVec, Sum.elim_inl, LinearMap.prodMap_apply, Matrix.zero_mulVec,
        add_zero, LinearEquiv.sumArrowLequivProdArrow_apply_fst]
      rfl
    · ext i
      simp only [f, g, Er, Ec, LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
        Matrix.fromBlocks_mulVec, Sum.elim_inr, LinearMap.prodMap_apply, Matrix.zero_mulVec,
        zero_add, LinearEquiv.sumArrowLequivProdArrow_apply_snd]
      rfl
  rw [Matrix.rank, Matrix.rank, Matrix.rank]
  calc Module.finrank K (LinearMap.range f)
      = Module.finrank K (Submodule.map Er.toLinearMap (LinearMap.range f)) :=
        (LinearEquiv.finrank_map_eq Er _).symm
    _ = Module.finrank K (LinearMap.range (Er.toLinearMap.comp f)) := by rw [LinearMap.range_comp]
    _ = Module.finrank K (LinearMap.range (g.comp Ec.toLinearMap)) := by rw [hfg]
    _ = Module.finrank K (LinearMap.range g) := by
        rw [LinearMap.range_comp_of_range_eq_top _ Ec.range]
    _ = Module.finrank K (LinearMap.range A.mulVecLin)
          + Module.finrank K (LinearMap.range B.mulVecLin) := by
        show Module.finrank K (LinearMap.range g) = _
        rw [show g = A.mulVecLin.prodMap B.mulVecLin from rfl, LinearMap.range_prodMap,
          finrank_submodule_prod]

/-! ## The binary direct sum of tuples

`dirSum A B : Tuple (fun l ↦ d l + d' l)` is the block-diagonal tuple
`(A ⊕ B)_t = fromBlocks A_t 0 0 B_t`, reindexed `Fin a ⊕ Fin b ≃ Fin (a+b)` so it lands in the
honest `Tuple` over the summed dimension vector. The sub-product of a direct sum is block-diagonal
(`submult_dirSum`), so its rank is additive (`rankPattern_dirSum`). -/

/-- The binary direct sum `A ⊕ B : Tuple (fun l ↦ d l + d' l)`: at each edge the block-diagonal
`fromBlocks A_t 0 0 B_t`, reindexed `Fin _ ⊕ Fin _ ≃ Fin (_ + _)`. -/
def dirSum {d d' : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) (B : Tuple (k := k) d') :
    Tuple (k := k) (fun l ↦ d l + d' l) :=
  fun t ↦ Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks (A t) 0 0 (B t))

/-- Reindexed block-diagonal matrices multiply block-wise:
`bd P Q * bd R S = bd (P*R) (Q*S)` (the off-diagonal blocks stay `0`). -/
theorem reindex_fromBlocks_mul {a₁ a₂ b₁ b₂ c₁ c₂ : ℕ}
    (P : Matrix (Fin a₁) (Fin b₁) k) (Q : Matrix (Fin a₂) (Fin b₂) k)
    (R : Matrix (Fin b₁) (Fin c₁) k) (S : Matrix (Fin b₂) (Fin c₂) k) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks P 0 0 Q)
        * Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks R 0 0 S)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks (P * R) 0 0 (Q * S)) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv.symm _, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

/-- The reindexed block-diagonal of two identities is the identity. -/
theorem reindex_fromBlocks_one {a₁ a₂ : ℕ} :
    (1 : Matrix (Fin (a₁ + a₂)) (Fin (a₁ + a₂)) k)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (fromBlocks (1 : Matrix (Fin a₁) (Fin a₁) k) 0 0 (1 : Matrix (Fin a₂) (Fin a₂) k)) := by
  rw [fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

/-- **The sub-product of a direct sum is block-diagonal.** `submult (A ⊕ B) i j` is the reindexed
block-diagonal of `submult A i j` and `submult B i j` — the structural fact behind rank additivity.
Proved by induction on the upper index through `submult_succ` + `reindex_fromBlocks_mul`. -/
theorem submult_dirSum {d d' : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) (B : Tuple (k := k) d')
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    submult (fun l ↦ d l + d' l) (dirSum A B) i j hij
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (fromBlocks (submult d A i j hij) 0 0 (submult d' B i j hij)) := by
  induction j using Fin.induction with
  | zero =>
    obtain rfl : i = 0 := Fin.le_zero_iff.mp hij
    rw [submult_self, submult_self, submult_self, reindex_fromBlocks_one]
  | succ p ih =>
    rcases eq_or_lt_of_le hij with heq | hlt
    · obtain rfl := heq
      rw [submult_self, submult_self, submult_self, reindex_fromBlocks_one]
    · have hip : i ≤ p.castSucc := by rw [Fin.le_castSucc_iff]; exact hlt
      rw [submult_succ (fun l ↦ d l + d' l) (dirSum A B) i p hip, ih hip,
        submult_succ d A i p hip, submult_succ d' B i p hip, dirSum, reindex_fromBlocks_mul]

/-- **Block-diagonal rank additivity for the rank pattern (over a field).** The rank pattern of a
direct sum is the sum of the rank patterns: `r_{ij}(A ⊕ B) = r_{ij}(A) + r_{ij}(B)`. The
direct-sum half of Prop 3.1b. -/
theorem rankPattern_dirSum {K : Type*} [Field K] {d d' : Fin (N + 1) → ℕ}
    (A : Tuple (k := K) d) (B : Tuple (k := K) d') (i j : Fin (N + 1)) (hij : i ≤ j) :
    rankPattern (fun l ↦ d l + d' l) (dirSum A B) i j hij
      = rankPattern d A i j hij + rankPattern d' B i j hij := by
  rw [rankPattern, rankPattern, rankPattern, submult_dirSum, Matrix.rank_reindex,
    rank_fromBlocks_zero_zero]

/-! ## The finite direct sum `⊕ M_{ij}^{m_{ij}}` and `rankPattern = cumul m` (rung 4b headline)

A Kostant array is encoded as a `List (Fin (N+1) × Fin (N+1))` of interval endpoints (each interval
`(i,j)` appearing with multiplicity = its count in the list). `intervalDirectSum L` folds `dirSum`
over the list; its rank pattern is `cumul N` of the list's multiplicity array — the full
interval-module side of Prop 3.1b. -/

/-- The dimension vector of the folded direct sum: `∑_{(a,b) ∈ L} e_{ab}`. -/
def foldDim : List (Fin (N + 1) × Fin (N + 1)) → (Fin (N + 1) → ℕ)
  | [] => fun _ ↦ 0
  | p :: ps => fun l ↦ intervalDim p.1 p.2 l + foldDim ps l

/-- The empty (zero-dimensional) tuple — the base of the direct-sum fold. -/
def zeroTuple : Tuple (k := k) (N := N) (fun _ ↦ 0) := fun _ ↦ Matrix.of (fun a _ ↦ a.elim0)

/-- The finite direct sum `⊕_{(a,b) ∈ L} M_{ab}` over a list of interval endpoints (multiplicities =
list multiplicities), as a block-diagonal `Tuple` over `foldDim L`. -/
noncomputable def intervalDirectSum :
    (L : List (Fin (N + 1) × Fin (N + 1))) → Tuple (k := k) (foldDim L)
  | [] => zeroTuple
  | p :: ps => dirSum (intervalModule p.1 p.2) (intervalDirectSum ps)

/-- The empty/zero-dimensional tuple has rank pattern `0`. -/
theorem rankPattern_zeroTuple [Nontrivial k] (i j : Fin (N + 1)) (hij : i ≤ j) :
    rankPattern (fun _ ↦ 0) (zeroTuple (k := k)) i j hij = 0 := by
  rw [rankPattern]
  have : IsEmpty (Fin ((fun _ : Fin (N + 1) ↦ 0) j)) := by simp only; infer_instance
  exact rank_eq_zero_of_isEmpty_rows _

/-- **Rank additivity over the fold.** The rank pattern of `⊕_{(a,b) ∈ L} M_{ab}` is the sum of the
single-module indicators over `L`. -/
theorem rankPattern_intervalDirectSum {K : Type*} [Field K]
    (L : List (Fin (N + 1) × Fin (N + 1))) (i j : Fin (N + 1)) (hij : i ≤ j) :
    rankPattern (foldDim L) (intervalDirectSum (k := K) L) i j hij
      = (L.map (fun p ↦
          rankPattern (intervalDim p.1 p.2) (intervalModule (k := K) p.1 p.2) i j hij)).sum := by
  induction L with
  | nil =>
    simp only [intervalDirectSum, List.map_nil, List.sum_nil]
    exact rankPattern_zeroTuple i j hij
  | cons p ps ih =>
    change rankPattern _ (dirSum _ _) i j hij = _
    rw [rankPattern_dirSum, ih, List.map_cons, List.sum_cons]

/-- `cumul` is additive in the array (it is a double `Finset.sum`). -/
theorem cumul_add (M : ℤ) (m₁ m₂ : ℤ → ℤ → ℤ) (i j : ℤ) :
    cumul M (fun a b ↦ m₁ a b + m₂ a b) i j = cumul M m₁ i j + cumul M m₂ i j := by
  simp only [cumul_apply, ← Finset.sum_add_distrib]

/-- `cumul N` of a single delta `δ_{(a,b)}` is the containment indicator
`[a ≤ i ∧ j ≤ b]` (for `a, b : Fin (N+1)`, so `0 ≤ a` and `b ≤ N` are automatic). -/
theorem cumul_singleDelta (a b : Fin (N + 1)) (i' j' : Fin (N + 1)) :
    cumul (N : ℤ) (singleDelta a b) (i' : ℤ) (j' : ℤ)
      = if a ≤ i' ∧ j' ≤ b then 1 else 0 := by
  rw [cumul_apply]
  simp only [singleDelta]
  rw [Finset.sum_comm]
  by_cases h : a ≤ i' ∧ j' ≤ b
  · rw [if_pos h, Finset.sum_eq_single (b : ℤ), Finset.sum_eq_single (a : ℤ)]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro x _ hx; rw [if_neg (by tauto)]
    · intro hbad; exact absurd (Finset.mem_Icc.mpr ⟨by positivity,
        by exact_mod_cast Fin.le_iff_val_le_val.mp h.1⟩) hbad
    · intro y _ hy; exact Finset.sum_eq_zero fun x _ ↦ if_neg (by tauto)
    · intro hbad; refine absurd (Finset.mem_Icc.mpr ⟨by exact_mod_cast Fin.le_iff_val_le_val.mp h.2,
        by exact_mod_cast Nat.lt_succ_iff.mp b.isLt⟩) hbad
  · rw [if_neg h]
    rw [not_and_or] at h
    apply Finset.sum_eq_zero
    intro y hy
    apply Finset.sum_eq_zero
    intro x hx
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    rw [Finset.mem_Icc] at hx hy
    rcases h with ha | hb
    · exact ha (Fin.le_iff_val_le_val.mpr (by exact_mod_cast hx.2))
    · exact hb (Fin.le_iff_val_le_val.mpr (by exact_mod_cast hy.1))

/-- The list's multiplicity array over `ℤ`: `m̄_{ab} = #{p ∈ L : p = (a,b)}` (as an integer
array indexed by `ℤ`, via the `Fin → ℤ` casts of the endpoints). -/
def multiplicityArray (L : List (Fin (N + 1) × Fin (N + 1))) : ℤ → ℤ → ℤ :=
  fun a b ↦ (L.map (fun p ↦ if a = (p.1 : ℤ) ∧ b = (p.2 : ℤ) then (1 : ℤ) else 0)).sum

/-- `multiplicityArray (p :: ps) = δ_p + multiplicityArray ps`. -/
theorem multiplicityArray_cons (p : Fin (N + 1) × Fin (N + 1))
    (ps : List (Fin (N + 1) × Fin (N + 1))) :
    multiplicityArray (p :: ps) = fun a b ↦ singleDelta p.1 p.2 a b + multiplicityArray ps a b := by
  funext a b; simp only [multiplicityArray, singleDelta, List.map_cons, List.sum_cons]

/-- **Prop 3.1b (interval-module side, headline).** The rank pattern of the finite direct sum
`⊕_{(a,b) ∈ L} M_{ab}` is `cumul N` of the list's multiplicity array:
`r_{ij}(⊕ M^m) = cumul N m̄ i j`, where `m̄` counts the interval multiplicities. Folds the
single-module indicator (`rankPattern_intervalModule`) and block-rank additivity
(`rankPattern_dirSum`) against the inversion engine's `cumul`. -/
theorem rankPattern_intervalDirectSum_eq_cumul {K : Type*} [Field K]
    (L : List (Fin (N + 1) × Fin (N + 1))) (i j : Fin (N + 1)) (hij : i ≤ j) :
    (rankPattern (foldDim L) (intervalDirectSum (k := K) L) i j hij : ℤ)
      = cumul (N : ℤ) (multiplicityArray L) (i : ℤ) (j : ℤ) := by
  rw [rankPattern_intervalDirectSum]
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, multiplicityArray, Nat.cast_zero, cumul_apply,
      Finset.sum_const_zero]
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons, multiplicityArray_cons, cumul_add, Nat.cast_add, ih,
      rankPattern_intervalModule, cumul_singleDelta, apply_ite (Nat.cast : ℕ → ℤ), Nat.cast_one,
      Nat.cast_zero]

section Witness

/-! ## Non-vacuity witnesses

`N = 2` (`Fin 3`), over `ℚ` (a field, for the additivity witness). The interval module `M_{02}` has
dimension vector `(1,1,1)` (all three vertices in `[0,2]`) and rank pattern `≡ 1` (every `[i',j']`
is contained in `[0,2]`). The direct sum `M_{00} ⊕ M_{11}` has rank pattern the sum of the two
indicators: `r_{00} = 1 + 0 = 1`, `r_{11} = 0 + 1 = 1`, `r_{02} = 0 + 0 = 0`. -/

/-- `M_{02}` over `Fin 3` has dimension vector `(1,1,1)`: all three vertices are `1`-dimensional. -/
example :
    (intervalDim (0 : Fin 3) 2 0, intervalDim (0 : Fin 3) 2 1, intervalDim (0 : Fin 3) 2 2)
      = (1, 1, 1) := by decide

/-- The rank pattern of `M_{02}` is the constant indicator `1` (every `[i',j'] ⊆ [0,2]`): here
`r_{00} = r_{02} = r_{11} = 1`. -/
example :
    rankPattern (intervalDim (0 : Fin 3) 2) (intervalModule (k := ℚ) 0 2) 0 0 (by decide) = 1
      ∧ rankPattern (intervalDim (0 : Fin 3) 2) (intervalModule (k := ℚ) 0 2) 0 2 (by decide) = 1
      ∧ rankPattern (intervalDim (0 : Fin 3) 2) (intervalModule (k := ℚ) 0 2) 1 1 (by decide) = 1 :=
  ⟨by rw [rankPattern_intervalModule]; decide,
   by rw [rankPattern_intervalModule]; decide,
   by rw [rankPattern_intervalModule]; decide⟩

/-- The indicator is `cumul` of the single delta `δ_{(0,2)}` on `M_{02}` at `(0,2)`. -/
example :
    (rankPattern (intervalDim (0 : Fin 3) 2) (intervalModule (k := ℚ) 0 2) 0 2 (by decide) : ℤ)
      = cumul (2 : ℤ) (singleDelta (0 : Fin 3) 2) 0 2 :=
  rankPattern_intervalModule_eq_cumul 0 2 (by decide)

/-- **Rank additivity on a concrete pair.** `M_{00} ⊕ M_{11}` over `Fin 3`/`ℚ`: the rank pattern is
the sum of the two single-module indicators (checked at `(0,0)`). -/
example :
    rankPattern _ (dirSum (intervalModule (k := ℚ) (0 : Fin 3) 0) (intervalModule 1 1)) 0 0
        (by decide)
      = rankPattern _ (intervalModule (k := ℚ) (0 : Fin 3) 0) 0 0 (by decide)
        + rankPattern _ (intervalModule (k := ℚ) (1 : Fin 3) 1) 0 0 (by decide) :=
  rankPattern_dirSum _ _ 0 0 (by decide)

/-- **The finite fold = `cumul`, on a concrete partition.** The direct sum
`M_{00} ⊕ M_{01} ⊕ M_{12} ⊕ M_{22}` over `Fin 3`/`ℚ` (the orbit of Ex 4.3, Kostant partition with
`m₀₀=m₀₁=m₁₂=m₂₂=1`) has rank pattern `= cumul 2 m̄` at `(0,2)` — here `r₀₂ = 0`. -/
example :
    (rankPattern (foldDim _) (intervalDirectSum (k := ℚ)
        [((0 : Fin 3), (0 : Fin 3)), (0, 1), (1, 2), (2, 2)]) 0 2 (by decide) : ℤ)
      = cumul (2 : ℤ)
          (multiplicityArray [((0 : Fin 3), (0 : Fin 3)), (0, 1), (1, 2), (2, 2)]) 0 2 :=
  rankPattern_intervalDirectSum_eq_cumul _ 0 2 (by decide)

end Witness

end DLNFibre.Core
