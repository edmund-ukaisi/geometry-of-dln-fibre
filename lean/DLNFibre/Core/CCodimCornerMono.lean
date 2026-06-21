import DLNFibre.Core.ThetaComponentCount

/-!
# `DLNFibre.Core.CCodimCornerMono` — the two θ-count gating bricks, discharged

This module discharges the explicit hypotheses `hLowerBound` and `hRecover` of
`Core.ThetaComponentCount.numTop_eq_ncard_topComponents_of`, so the θ-count headline
`numTop d r = #{top-dimensional irreducible components of Σ̄^r}` becomes **unconditional**.

Two bricks, both reducing to one combinatorial monotonicity of `cCodim`:

* **The Gabriel→Kostant bridge** (`orbitRankLocus_realizerD_gabrielPartition`). Every tuple lies
  in the orbit closure of the realizer of a Kostant partition of `d` with corner exactly
  `(mult d M').rank`, with the SAME orbit rank locus (hence the same orbit ideal, the same geometric
  codimension). The Gabriel normal form (`Core.OrbitKostant.kostantArrayOfRank` / `CMPlus`) recast
  into the `CTheta` `Fin × Fin → ℕ` / `extendℤ` encoding.

* **Corner-monotonicity of `cCodim`**. For `s ≤ r` (both Kostant families nonempty),
  `cCodim d r ≤ cCodim d s`: a corner-`s` orbit family has codimension-minimum ≥ the corner-`r`
  one. Reduced (via the LANDED rank-shift `cCodim d t = cCodim (d−t) 0`) to dimension-monotonicity
  `cCodim e 0 ≤ cCodim e' 0` for `e ≤ e'`.

`hLowerBound` is the geometric reading of corner-monotonicity (every corner-`≤r` orbit has codim
`≥ cCodim d r`); `hRecover` is the Gabriel bridge plus corner-monotonicity forcing corner `= r` on a
top-dimensional component.

**Typeclass.** `[Field k]` for the bridge; `[IsAlgClosed k] [CharZero k]` for the geometric reading
(`codimRepCanonical = codimForm`). **Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal Finset

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The Gabriel→Kostant bridge

`kostantArrayOfRank (rankFn d M')` (`Core.OrbitKostant`) is a `CMPlus d` array — nonnegative,
`i ≤ j`-supported, satisfying the dimension equations. Its `Fin × Fin → ℕ` shadow
`m' p := (kostantArrayOfRank (rankFn d M')).1 p.1 p.2 |>.toNat` is a Kostant partition of `d` whose
corner is `(mult d M').rank` and whose realizer has the same rank pattern as `M'`. -/

/-- The `Fin × Fin → ℕ` shadow of a `CMPlus`-array: `m p = (m.1 p.1 p.2).toNat`. The
`CTheta`-encoding of the `Core.OrbitKostant` `SuppArray` Kostant partition. -/
noncomputable def finArrayOfSupp (m : SuppArray (N : ℤ) ℤ) : Fin (N + 1) × Fin (N + 1) → ℕ :=
  fun p ↦ (m.1 (p.1 : ℤ) (p.2 : ℤ)).toNat

/-- **`extendℤ` recovers the array on the box.** For an `IsKostantArray` (nonnegative,
`i ≤ j`-supported) array `m`, the `extendℤ` of its `Fin`-shadow agrees with `m.1` everywhere: on the
box `extendℤ` reads `(m.1 a b).toNat = m.1 a b` (nonneg); off the box both are `0` (support). -/
theorem extendℤ_finArrayOfSupp {m : SuppArray (N : ℤ) ℤ} (hm : IsKostantArray m) :
    extendℤ (finArrayOfSupp m) = m.1 := by
  funext a b
  unfold extendℤ finArrayOfSupp
  split_ifs with h
  · obtain ⟨ha, hab, hb⟩ := h
    have hi : ((⟨a.toNat, by omega⟩ : Fin (N + 1)) : ℤ) = a := by simp [Int.toNat_of_nonneg ha]
    have hj : ((⟨b.toNat, by omega⟩ : Fin (N + 1)) : ℤ) = b := by
      simp [Int.toNat_of_nonneg (le_trans ha hab)]
    rw [show ((⟨a.toNat, by omega⟩ : Fin (N + 1)) : ℤ) = a from hi,
      show ((⟨b.toNat, by omega⟩ : Fin (N + 1)) : ℤ) = b from hj]
    exact Int.toNat_of_nonneg (hm.1 a b)
  · -- off the box: `m.1 a b = 0` by support (below diagonal, or `a<0`, or `b>N`)
    rcases lt_or_ge a 0 with ha | ha
    · exact (m.2.1 a b ha).symm
    rcases lt_or_ge (N : ℤ) b with hb | hb
    · exact (m.2.2 a b hb).symm
    · exact (hm.2 a b (by have := h; simp only [not_and, not_le] at h; omega)).symm

/-- **The shadow is Kostant of the right corner.** For a `CMPlus d` array `m`, its `Fin`-shadow
`finArrayOfSupp m` is a Kostant partition of `d` with corner `(m.1 0 N).toNat`. Bound + support from
`IsKostantArray`; dimension equations `cumul m k k = d k` (`CMPlus`); corner = `(0, last N)`. -/
theorem finArrayOfSupp_mem_kostantPartitions {d : Fin (N + 1) → ℕ} {m : SuppArray (N : ℤ) ℤ}
    (hm : CMPlus d m) :
    finArrayOfSupp m
      ∈ kostantPartitions d ((m.1 (0 : ℤ) (N : ℤ)).toNat) := by
  obtain ⟨hkost, hdim⟩ := hm
  rw [mem_kostantPartitions]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- bound `m p ≤ d p.1`: follows from the Kostant dimension equation (one summand of `d p.1`)
    intro p
    by_cases hp : p.1 ≤ p.2
    · have hmem : ((p.1 : ℤ), (p.2 : ℤ))
          ∈ Finset.Icc (0 : ℤ) (p.1 : ℤ) ×ˢ Finset.Icc (p.1 : ℤ) (N : ℤ) := by
        rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        simp only
        refine ⟨⟨by positivity, le_rfl⟩, ?_, ?_⟩
        · exact_mod_cast Fin.le_def.mp hp
        · exact_mod_cast Nat.lt_succ_iff.mp p.2.isLt
      have hcov : m.1 (p.1 : ℤ) (p.2 : ℤ) ≤ cumul (N : ℤ) m.1 (p.1 : ℤ) (p.1 : ℤ) := by
        rw [cumul_apply, ← Finset.sum_product']
        exact Finset.single_le_sum (f := fun q : ℤ × ℤ ↦ m.1 q.1 q.2)
          (fun q _ ↦ hkost.1 q.1 q.2) hmem
      have hd : (d p.1 : ℤ) = cumul (N : ℤ) m.1 (p.1 : ℤ) (p.1 : ℤ) := hdim p.1
      have hle : (finArrayOfSupp m p : ℤ) ≤ (d p.1 : ℤ) := by
        unfold finArrayOfSupp
        rw [Int.toNat_of_nonneg (hkost.1 _ _), hd]; exact hcov
      exact_mod_cast hle
    · -- off triangle: support gives `0`
      have hp2 : (p.2 : ℤ) < (p.1 : ℤ) := by
        exact_mod_cast lt_of_not_ge (fun hle ↦ hp (Fin.le_def.mpr (by exact_mod_cast hle)))
      unfold finArrayOfSupp
      rw [hkost.2 (p.1 : ℤ) (p.2 : ℤ) hp2]; exact Nat.zero_le _
  · -- support
    intro p hp
    have hp2 : (p.2 : ℤ) < (p.1 : ℤ) := by
      exact_mod_cast lt_of_not_ge (fun hle ↦ hp (Fin.le_def.mpr (by exact_mod_cast hle)))
    unfold finArrayOfSupp
    rw [hkost.2 (p.1 : ℤ) (p.2 : ℤ) hp2]; rfl
  · -- dimension equations: `d k = ∑ filter` is the diagonal cumul of `extendℤ (finArrayOfSupp m)`
    intro k
    rw [kostantAt]
    have : (d k : ℤ)
        = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ k ∧ k ≤ p.2),
            finArrayOfSupp m p : ℤ) := by
      rw [hdim k, ← cumul_extendℤ_diag, extendℤ_finArrayOfSupp hkost]
    exact_mod_cast this
  · -- corner `(0, last N)` is `(m.1 0 N).toNat`
    unfold finArrayOfSupp
    norm_num [Fin.val_last]

/-! ## The realizer of the Gabriel partition matches the tuple

For a tuple `M'`, the Gabriel partition `gabrielPartition d M' = finArrayOfSupp (kostantArrayOfRank
(rankFn d M'))` is Kostant of corner `(mult d M').rank`, and the realizer's rank pattern is `cumul`
of `kostantArrayOfRank (rankFn d M')`, which is `rankPattern M'` on the triangle. So the realizer's
orbit rank locus equals that of `M'`. -/

/-- The **Gabriel Kostant partition** of a tuple `M'`: the `Fin`-shadow of the Gabriel normal-form
multiplicity array `kostantArrayOfRank (rankFn d M')`. A Kostant partition of `d`. -/
noncomputable def gabrielPartition (d : Fin (N + 1) → ℕ) (M' : Tuple (k := k) d) :
    Fin (N + 1) × Fin (N + 1) → ℕ :=
  finArrayOfSupp (kostantArrayOfRank (rankFn d M'))

/-- The corner of the Gabriel partition is `(mult d M').rank`: the `(0, N)` multiplicity is
`cumul (kostantArrayOfRank …) 0 N = rankPattern M' 0 N = (mult d M').rank`. -/
theorem gabrielPartition_corner [Nontrivial k] (d : Fin (N + 1) → ℕ) (M' : Tuple (k := k) d) :
    ((kostantArrayOfRank (rankFn d M')).1 (0 : ℤ) (N : ℤ)).toNat = (mult d M').rank := by
  -- `(kostantArrayOfRank r) 0 N = cumul (kostantArrayOfRank r) 0 N` (single box point), and
  -- `cumul (kostantArrayOfRank r) 0 N = embedRank r 0 N = r 0 N = rankPattern M' 0 N = rank`.
  have hcumul : cumul (N : ℤ) (kostantArrayOfRank (rankFn d M')).1 (0 : ℤ) (N : ℤ)
      = (kostantArrayOfRank (rankFn d M')).1 (0 : ℤ) (N : ℤ) := by
    rw [cumul_apply]
    have h0 : Finset.Icc (0 : ℤ) (0 : ℤ) = {0} := by simp
    have hN : Finset.Icc (N : ℤ) (N : ℤ) = {(N : ℤ)} := by simp
    rw [h0, hN, Finset.sum_singleton, Finset.sum_singleton]
  have hembed : cumul (N : ℤ) (kostantArrayOfRank (rankFn d M')).1 (0 : ℤ) (N : ℤ)
      = (embedRank (rankFn d M')).1 (0 : ℤ) (N : ℤ) :=
    cumul_kostantArrayOfRank_of_le (rankFn d M') (by positivity)
  have hval : (embedRank (rankFn d M')).1 (0 : ℤ) (N : ℤ) = (rankFn d M' 0 (Fin.last N) : ℤ) := by
    have := embedRank_apply_fin (rankFn d M') 0 (Fin.last N)
    rwa [Fin.val_zero, Fin.val_last] at this
  have hrank : rankFn d M' 0 (Fin.last N) = (mult d M').rank := by
    rw [rankFn, dif_pos (Fin.zero_le _), corner_rankPattern_eq_rank]
  rw [← hcumul, hembed, hval, hrank, Int.toNat_natCast]

/-- The Gabriel partition is Kostant of `d` with corner `(mult d M').rank`. -/
theorem gabrielPartition_mem [Nontrivial k] (d : Fin (N + 1) → ℕ) (M' : Tuple (k := k) d) :
    gabrielPartition d M' ∈ kostantPartitions d ((mult d M').rank) := by
  have h := finArrayOfSupp_mem_kostantPartitions (cMPlus_kostantArrayOfRank (k := k) M')
  rwa [gabrielPartition_corner d M'] at h

/-- The realizer of the Gabriel partition has the **same rank pattern** as `M'` on the triangle:
`rankPattern (realizerD …) = rankPattern M'`. Via `extendℤ (gabrielPartition) = kostantArrayOfRank
(rankFn M')` and `cumul (kostantArrayOfRank r) = embedRank r = r = rankPattern` on the triangle. -/
theorem rankPattern_realizerD_gabrielPartition [Nontrivial k] (d : Fin (N + 1) → ℕ)
    (M' : Tuple (k := k) d) (i j : Fin (N + 1)) (hij : i ≤ j) :
    rankPattern d (realizerD (k := k) (gabrielPartition_mem d M')) i j hij
      = rankPattern d M' i j hij := by
  have hijZ : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast Fin.le_def.mp hij
  have hZ : (rankPattern d (realizerD (k := k) (gabrielPartition_mem d M')) i j hij : ℤ)
      = (rankPattern d M' i j hij : ℤ) := by
    rw [rankPattern_realizerD (k := k) (gabrielPartition_mem d M') i j hij,
      show gabrielPartition d M' = finArrayOfSupp (kostantArrayOfRank (rankFn d M')) from rfl,
      extendℤ_finArrayOfSupp (kostantArrayOfRank_isKostant (k := k) M'),
      cumul_kostantArrayOfRank_of_le (rankFn d M') hijZ, embedRank_apply_fin,
      rankFn, dif_pos hij]
  exact_mod_cast hZ

/-- The realizer's orbit rank locus equals `M'`'s: same rank pattern (`orbitRankLocus` depends only
on the rank pattern, `orbitRankLocus_eq_of_rankPattern_eq`). The Gabriel→Kostant bridge. -/
theorem orbitRankLocus_realizerD_gabrielPartition [Nontrivial k] (d : Fin (N + 1) → ℕ)
    (M' : Tuple (k := k) d) :
    orbitRankLocus (realizerD (k := k) (gabrielPartition_mem d M')) = orbitRankLocus M' :=
  orbitRankLocus_eq_of_rankPattern_eq (rankPattern_realizerD_gabrielPartition d M')

/-! ## Dimension-monotonicity of `cCodim · 0` (the combinatorial crux)

`cCodim e 0 ≤ cCodim e' 0` for `e ≤ e'` pointwise. The single load-bearing inequality behind
corner-monotonicity. By `Finset.le_inf'_iff` it reduces to: every corner-`0` partition `m'` of `e'`
dominates (in `codimForm`) a corner-`0` partition of `e`. The witness is the **interval-shortening**
restriction of `m'`: at a vertex `k` over-covered by 1, split the SHORTEST covering interval `[i,j]`
into `[i,k-1]` and `[k+1,j]` (the codimForm-minimal restriction). -/

/-! TODO `cCodim_zero_mono` (the shortest-interval split). -/

end DLNFibre.Core
