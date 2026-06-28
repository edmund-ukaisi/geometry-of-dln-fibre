import DLNFibre.Core.ThetaComponentCount

/-!
# `DLNFibre.Core.CCodimCornerMono` — the two θ-count gating bricks, reduced

This module **reduces** the two explicit hypotheses `hLowerBound` and `hRecover` of
`Core.ThetaComponentCount.numTop_eq_ncard_topComponents_of` to a *single* combinatorial monotonicity
— the dimension-monotonicity of `cCodim · 0` (`hMono` / `hMonoStrict` below). Those two combinatorial
monotonicities are now **proved in Lean** (`Core.CCodimZeroMono.cCodim_zero_mono`, weak;
`Core.CCodimZeroStrict.cCodim_zero_strict`, strict all-vertex — both via the shortest-interval-split
construction), so the θ-count headline `Core.CCodimZeroStrict.numTop_eq_ncard_topComponents` is now
**unconditional** (no open hypothesis), axiom-clean. The two *geometric* hypotheses of thread 05 were
thereby first replaced by one clean `CTheta`-level inequality, and that inequality is now discharged.

Two bricks, both reducing to that one combinatorial monotonicity of `cCodim`:

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

**Typeclass.** `[Field k]` for the bridge; `[CharZero k] [Infinite k]` for the geometric reading
(`codimRepCanonical = codimForm`; no algebraic closedness). **Dependency rule:** `Core` only — never
import `DLNFibre.DLN`.
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

/-! ## The diagonal partition (corner-`0` nonemptiness, for free)

The all-singletons partition `m(k,k) = e_k` (else `0`) is Kostant for `e` with corner `0` (when
`N ≥ 1`, so `(0, last N) ≠ (k, k)`): the dimension equation at `k` reads `e_k` (only `(k,k)` covers
`k` among the diagonal intervals), and the corner is `0`. So `kostantPartitions e 0` is nonempty
unconditionally. -/

/-- The all-singletons partition `diagPart e (k, l) = if k = l then e k else 0`. -/
def diagPart (e : Fin (N + 1) → ℕ) : Fin (N + 1) × Fin (N + 1) → ℕ :=
  fun p ↦ if p.1 = p.2 then e p.1 else 0

/-- The diagonal partition is Kostant for `e` with corner `0` (needs `N ≥ 1` so the corner
`(0, last N)` is off the diagonal). -/
theorem diagPart_mem {e : Fin (N + 1) → ℕ} (hN : 1 ≤ N) :
    diagPart e ∈ kostantPartitions e 0 := by
  rw [mem_kostantPartitions]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- bound `diagPart e p ≤ e p.1`
    intro p; unfold diagPart; split_ifs with h
    · rw [h]
    · exact Nat.zero_le _
  · -- support: off the triangle `p.1 > p.2`, so `p.1 ≠ p.2`
    intro p hp; unfold diagPart; rw [if_neg (fun he ↦ hp (le_of_eq he))]
  · -- dimension equation: only `(k, k)` in the filter has nonzero `diagPart`
    intro k; rw [kostantAt]
    rw [Finset.sum_eq_single (k, k)]
    · unfold diagPart; rw [if_pos rfl]
    · intro p hp hpne
      unfold diagPart; split_ifs with h
      · -- `p.1 = p.2` and `p ∈ filter k` (so `p.1 ≤ k ≤ p.2`) but `p ≠ (k,k)` is impossible
        rw [Finset.mem_filter] at hp
        obtain ⟨-, h1, h2⟩ := hp
        exact absurd (Prod.ext (le_antisymm h1 (h ▸ h2)) (h ▸ le_antisymm h1 (h ▸ h2))) hpne
      · rfl
    · intro hbad
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, le_rfl⟩) hbad
  · -- corner `(0, last N)` is off-diagonal (`0 ≠ last N` since `N ≥ 1`)
    unfold diagPart
    rw [if_neg (fun h ↦ by
      have : (0 : ℕ) = N := by have := congrArg Fin.val h; simpa [Fin.val_last] using this
      omega)]

/-- `kostantPartitions e 0` is nonempty for `N ≥ 1` (the diagonal partition). -/
theorem kostantPartitions_zero_nonempty {e : Fin (N + 1) → ℕ} (hN : 1 ≤ N) :
    (kostantPartitions e 0).Nonempty :=
  ⟨diagPart e, diagPart_mem hN⟩

/-- `kostantPartitions d r` is nonempty for `N ≥ 1` whenever `r ≤ d k` at every vertex: the corner
`m_{0N} = r` plus the diagonal `m_{kk} = d_k − r`. (At `N = 0` the corner is the diagonal, forcing
`r = d₀`, so `1 ≤ N` is needed.) -/
theorem kostantPartitions_nonempty_of_le {d : Fin (N + 1) → ℕ} {r : ℕ}
    (hN : 1 ≤ N) (hr : ∀ k, r ≤ d k) : (kostantPartitions d r).Nonempty := by
  have h0 := kostantPartitions_zero_nonempty (e := dminus d r) hN
  rw [kostantPartitions_dminus_eq_image hr] at h0
  exact h0.of_image

/-! ## Corner-monotonicity from the dimension-monotonicity

`cCodim d r ≤ cCodim d s` for `s ≤ r`, via the LANDED rank-shift `cCodim d t = cCodim (d−t) 0` and
the dimension-monotonicity `cCodim e 0 ≤ cCodim e' 0` for `e ≤ e'` (since `r ≥ s ⟹ d−r ≤ d−s`). The
`r ≤ d k` / `s ≤ d k` hypotheses are automatic from corner partitions existing. -/

/-- A Kostant partition of `d` with corner `r` forces `r ≤ d k` at every vertex (the corner `[0,N]`
covers `k`, so `r = m_{0N}` is one summand of `d k`). -/
theorem corner_le_dim_of_mem {d : Fin (N + 1) → ℕ} {r : ℕ}
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} (hm : m ∈ kostantPartitions d r) (k : Fin (N + 1)) :
    r ≤ d k := by
  obtain ⟨-, -, hk, hcorner⟩ := mem_kostantPartitions.mp hm
  rw [← hcorner, hk k]
  exact Finset.single_le_sum (fun q _ ↦ Nat.zero_le _) (corner_mem_filter k)

/-- `dminus` is pointwise antitone in the corner: `s ≤ r ⟹ dminus d r k ≤ dminus d s k`. -/
theorem dminus_anti {d : Fin (N + 1) → ℕ} {s r : ℕ} (hsr : s ≤ r) (k : Fin (N + 1)) :
    dminus d r k ≤ dminus d s k := by
  unfold dminus; omega

/-- **Corner-monotonicity from dimension-monotonicity.** Given the dimension-monotonicity of
`cCodim · 0` (`hMono`: `e ≤ e' ⟹ cCodim e 0 ≤ cCodim e' 0`), the codimension is corner-antitone:
`cCodim d r ≤ cCodim d s` for `s ≤ r`. By the LANDED rank-shift both sides are `cCodim (d−·) 0`, and
`d−r ≤ d−s`. The rank-shift hypotheses `t ≤ d k` come from the corner partitions existing
(`corner_le_dim_of_mem`). -/
theorem cCodim_corner_anti_of
    (hMono : ∀ {e e' : Fin (N + 1) → ℕ} (he : (kostantPartitions e 0).Nonempty)
      (he' : (kostantPartitions e' 0).Nonempty), (∀ k, e k ≤ e' k) →
      cCodim e 0 he ≤ cCodim e' 0 he')
    {d : Fin (N + 1) → ℕ} {s r : ℕ} (hsr : s ≤ r)
    (hs : (kostantPartitions d s).Nonempty) (hr : (kostantPartitions d r).Nonempty) :
    cCodim d r hr ≤ cCodim d s hs := by
  obtain ⟨ms, hms⟩ := id hs
  obtain ⟨mr, hmr⟩ := id hr
  have hrd : ∀ k, r ≤ d k := corner_le_dim_of_mem hmr
  have hsd : ∀ k, s ≤ d k := corner_le_dim_of_mem hms
  have hr0 : (kostantPartitions (dminus d r) 0).Nonempty := by
    rw [kostantPartitions_dminus_eq_image hrd]; exact hr.image dropCorner
  have hs0 : (kostantPartitions (dminus d s) 0).Nonempty := by
    rw [kostantPartitions_dminus_eq_image hsd]; exact hs.image dropCorner
  have er : cCodim d r hr = cCodim (dminus d r) 0 hr0 := (cCodim_rankShift hrd hr0 hr).symm
  have es : cCodim d s hs = cCodim (dminus d s) 0 hs0 := (cCodim_rankShift hsd hs0 hs).symm
  rw [er, es]
  exact hMono hr0 hs0 (dminus_anti hsr)

/-! ## The geometric lower bound `hLowerBound`, from corner-monotonicity

For a corner-`≤ r` tuple `M'`, the geometric codimension of its orbit closure is `codimForm` of the
Gabriel Kostant partition (corner `s = (mult M').rank ≤ r`), `≥ cCodim d s ≥ cCodim d r`. -/

/-- **`hLowerBound`, from corner-monotonicity.** Every corner-`≤ r` orbit closure has codimension
`≥ cCodim d r`. Via the Gabriel bridge (`codimRep(Ō_{M'}) = codimForm (extendℤ (gabrielPartition))`,
corner `(mult M').rank`), `Finset.inf'_le` (`codimForm ≥ cCodim d s`), and corner-monotonicity
(`cCodim d r ≤ cCodim d s` for `s ≤ r`). -/
theorem cCodim_le_codimRepCanonical_of [CharZero k] [Infinite k]
    (hMono : ∀ {e e' : Fin (N + 1) → ℕ} (he : (kostantPartitions e 0).Nonempty)
      (he' : (kostantPartitions e' 0).Nonempty), (∀ k, e k ≤ e' k) →
      cCodim e 0 he ≤ cCodim e' 0 he')
    (d : Fin (N + 1) → ℕ) (r : ℕ) (hr : (kostantPartitions d r).Nonempty)
    (M' : Tuple (k := k) d) (hM' : (mult d M').rank ≤ r) :
    ((cCodim d r hr).toNat : ℕ∞) ≤ codimRepCanonical (orbitRankLocus M') := by
  set s := (mult d M').rank with hsdef
  have hms : gabrielPartition d M' ∈ kostantPartitions d s := gabrielPartition_mem d M'
  have hs : (kostantPartitions d s).Nonempty := ⟨_, hms⟩
  -- the geometric codim of `Ō_{M'}` is `codimForm (extendℤ (gabrielPartition))`
  have hgeo : ((codimRepCanonical (orbitRankLocus M')).toNat : ℤ)
      = codimForm N (extendℤ (gabrielPartition d M')) := by
    rw [← orbitRankLocus_realizerD_gabrielPartition (k := k) d M',
      codimRepCanonical_orbitRankLocus_realizerD hms]
  -- `cCodim d s ≤ codimForm (gabrielPartition)` (inf'_le); `cCodim d r ≤ cCodim d s`
  have hinf : cCodim d s hs ≤ codimForm N (extendℤ (gabrielPartition d M')) :=
    Finset.inf'_le _ hms
  have hanti : cCodim d r hr ≤ cCodim d s hs := cCodim_corner_anti_of hMono hM' hs hr
  -- assemble: `cCodim d r ≤ codimForm = codimRep.toNat`, then cast to `ℕ∞`
  have hZ : (cCodim d r hr) ≤ ((codimRepCanonical (orbitRankLocus M')).toNat : ℤ) := by
    rw [hgeo]; exact le_trans hanti hinf
  have hfin : codimRepCanonical (orbitRankLocus M') ≠ ⊤ := by
    rw [codimRepCanonical_orbitRankLocus_eq_height]
    exact Ideal.height_ne_top (isPrime_vanishingIdeal_orbitRankLocus _).ne_top
  -- `(cCodim d r).toNat ≤ codimRep.toNat` as ℕ, then `≤` as ℕ∞
  have hcr_nonneg : 0 ≤ cCodim d r hr := by
    rw [cCodim_eq_inf_geomCodim (k := k), Finset.le_inf'_iff]
    exact fun m' _ ↦ Int.natCast_nonneg _
  have hnat : (cCodim d r hr).toNat ≤ (codimRepCanonical (orbitRankLocus M')).toNat := by omega
  calc ((cCodim d r hr).toNat : ℕ∞)
      ≤ ((codimRepCanonical (orbitRankLocus M')).toNat : ℕ∞) := by exact_mod_cast hnat
    _ = codimRepCanonical (orbitRankLocus M') := ENat.coe_toNat hfin

/-! ## Strict corner-monotonicity and the recovery `hRecover`

`cCodim d r < cCodim d s` for `s < r`, via the rank-shift and the STRICT all-vertex dimension-drop
`cCodim e 0 < cCodim e' 0` when `e < e'` at every vertex (`d−r < d−s` when `r > s`).
Strict corner-monotonicity forces a top-dimensional component (codim `= cCodim d r`) onto corner
exactly `r`: a corner-`s` orbit (`s < r`) has codim `cCodim d s > cCodim d r` (strict), so cannot be
top-dimensional. This is what `hRecover` needs for the top component. -/

/-- **Strict corner-monotonicity, from the strict all-vertex dimension-drop.** Given `hMonoStrict`
(`e < e' at every vertex ⟹ cCodim e 0 < cCodim e' 0`), for `s < r` (both nonempty),
`cCodim d r < cCodim d s` (since `d−r < d−s` at every vertex). -/
theorem cCodim_corner_strict_of
    (hMonoStrict : ∀ {e e' : Fin (N + 1) → ℕ} (he : (kostantPartitions e 0).Nonempty)
      (he' : (kostantPartitions e' 0).Nonempty), (∀ k, e k < e' k) →
      cCodim e 0 he < cCodim e' 0 he')
    {d : Fin (N + 1) → ℕ} {s r : ℕ} (hsr : s < r)
    (hs : (kostantPartitions d s).Nonempty) (hr : (kostantPartitions d r).Nonempty) :
    cCodim d r hr < cCodim d s hs := by
  obtain ⟨ms, hms⟩ := id hs
  obtain ⟨mr, hmr⟩ := id hr
  have hrd : ∀ k, r ≤ d k := corner_le_dim_of_mem hmr
  have hsd : ∀ k, s ≤ d k := corner_le_dim_of_mem hms
  have hr0 : (kostantPartitions (dminus d r) 0).Nonempty := by
    rw [kostantPartitions_dminus_eq_image hrd]; exact hr.image dropCorner
  have hs0 : (kostantPartitions (dminus d s) 0).Nonempty := by
    rw [kostantPartitions_dminus_eq_image hsd]; exact hs.image dropCorner
  have er : cCodim d r hr = cCodim (dminus d r) 0 hr0 := (cCodim_rankShift hrd hr0 hr).symm
  have es : cCodim d s hs = cCodim (dminus d s) 0 hs0 := (cCodim_rankShift hsd hs0 hs).symm
  rw [er, es]
  -- `dminus d r k = d k − r < d k − s = dminus d s k` at every vertex (since `r > s ≤ d k`)
  refine hMonoStrict hr0 hs0 (fun k ↦ ?_)
  have := hrd k; unfold dminus; omega

/-- **`hRecover`, from strict corner-monotonicity.** Every top-dimensional component `p` (a minimal
prime of `sigmaIdeal d r` of height `cCodim d r`) is the orbit ideal of *some corner-`r`* Kostant
partition. From G3 (`minimalPrimes_sigmaIdeal_eq`) `p = vanishingIdeal (Ō_{M'})` for a corner-`≤ r`
tuple `M'`; the Gabriel partition has corner `s = (mult M').rank ≤ r` and the same orbit ideal; the
top-dimensional height `cCodim d r = codimForm (gabrielPartition) ≥ cCodim d s` with strict
corner-monotonicity (`s < r ⟹ cCodim d r < cCodim d s`) forces `s = r`. -/
theorem exists_kostantPartition_partitionIdeal_eq_of [CharZero k] [Infinite k]
    (hMonoStrict : ∀ {e e' : Fin (N + 1) → ℕ} (he : (kostantPartitions e 0).Nonempty)
      (he' : (kostantPartitions e' 0).Nonempty), (∀ k, e k < e' k) →
      cCodim e 0 he < cCodim e' 0 he')
    (d : Fin (N + 1) → ℕ) (r : ℕ) (hr : (kostantPartitions d r).Nonempty)
    (p : Ideal (MvPolynomial (RepCoord d) k)) (hp : p ∈ topComponents (k := k) d r hr) :
    ∃ m ∈ kostantPartitions d r, partitionIdeal (k := k) d r m = p := by
  -- G3: `p` is a corner-`≤ r` orbit ideal `vanishingIdeal (Ō_{M'})`
  rw [topComponents, Set.mem_setOf_eq, minimalPrimes_sigmaIdeal_eq] at hp
  obtain ⟨⟨⟨M', hM', hpeq⟩, -⟩, hheight⟩ := hp
  simp only at hpeq
  -- the Gabriel partition of `M'`: Kostant of corner `s = (mult M').rank ≤ r`, same orbit ideal
  set s := (mult d M').rank with hsdef
  have hms : gabrielPartition d M' ∈ kostantPartitions d s := gabrielPartition_mem d M'
  have hs : (kostantPartitions d s).Nonempty := ⟨_, hms⟩
  have hlocus : orbitRankLocus (realizerD (k := k) hms) = orbitRankLocus M' :=
    orbitRankLocus_realizerD_gabrielPartition (k := k) d M'
  have hideal : partitionIdeal (k := k) d s (gabrielPartition d M') = p := by
    rw [partitionIdeal_of_mem hms, hlocus, hpeq]
  -- `p.height = codimRep (Ō_{M'}).toNat = codimForm (gabrielPartition)` and `= cCodim d r`
  have hcodimForm : (p.height.toNat : ℤ) = codimForm N (extendℤ (gabrielPartition d M')) := by
    rw [← hpeq, ← codimRepCanonical_orbitRankLocus_eq_height, ← hlocus,
      codimRepCanonical_orbitRankLocus_realizerD hms]
  have hpheightVal : p.height = ((cCodim d r hr).toNat : ℕ∞) := hheight
  -- corner `s = r`: else `s < r` gives `cCodim d r < cCodim d s ≤ codimForm = cCodim d r`
  have hsr : s ≤ r := hM'
  have hsEqR : s = r := by
    rcases lt_or_eq_of_le hsr with hlt | heq
    · exfalso
      -- `codimForm (gabrielPartition) = p.height.toNat = cCodim d r` (top-dim height)
      have hcf_eq : codimForm N (extendℤ (gabrielPartition d M')) = (cCodim d r hr : ℤ) := by
        have hcr_nonneg : 0 ≤ cCodim d r hr := by
          rw [cCodim_eq_inf_geomCodim (k := k), Finset.le_inf'_iff]
          exact fun m' _ ↦ Int.natCast_nonneg _
        rw [← hcodimForm, hpheightVal, ENat.toNat_coe]; omega
      -- `cCodim d s ≤ codimForm = cCodim d r` and strict `cCodim d r < cCodim d s` ⟹ contradiction
      have hinf : cCodim d s hs ≤ codimForm N (extendℤ (gabrielPartition d M')) :=
        Finset.inf'_le _ hms
      have hstrict : cCodim d r hr < cCodim d s hs := cCodim_corner_strict_of hMonoStrict hlt hs hr
      rw [hcf_eq] at hinf
      exact absurd hinf (not_le.mpr hstrict)
    · exact heq
  -- `gabrielPartition ∈ kostantPartitions d r` and `partitionIdeal d r = p`
  subst hsEqR
  exact ⟨gabrielPartition d M', hms, hideal⟩

/-! ## The θ-count headline, reduced to the two dimension-monotonicities

Both gating hypotheses of `numTop_eq_ncard_topComponents_of` discharge from the dimension-mono
of `cCodim · 0`: `hLowerBound` from the weak `hMono`, `hRecover` from strict `hMonoStrict`. So the
headline `numTop d r = #top-dim components` holds given those two combinatorial monotonicities. -/

/-- **θ-count headline, reduced to dimension-monotonicity.** Given the weak (`hMono`) and strict
(`hMonoStrict`) dimension-monotonicities of `cCodim · 0`, `numTop d r = #{top-dim irreducible
components of Σ̄^r}` — the two corner-selection hypotheses of `numTop_eq_ncard_topComponents_of`
discharged. -/
theorem numTop_eq_ncard_topComponents_of_dimMono [CharZero k] [Infinite k]
    (hMono : ∀ {e e' : Fin (N + 1) → ℕ} (he : (kostantPartitions e 0).Nonempty)
      (he' : (kostantPartitions e' 0).Nonempty), (∀ k, e k ≤ e' k) →
      cCodim e 0 he ≤ cCodim e' 0 he')
    (hMonoStrict : ∀ {e e' : Fin (N + 1) → ℕ} (he : (kostantPartitions e 0).Nonempty)
      (he' : (kostantPartitions e' 0).Nonempty), (∀ k, e k < e' k) →
      cCodim e 0 he < cCodim e' 0 he')
    (d : Fin (N + 1) → ℕ) (r : ℕ) (hr : (kostantPartitions d r).Nonempty) :
    numTop d r hr = (topComponents (k := k) d r hr).ncard :=
  numTop_eq_ncard_topComponents_of d r hr
    (fun M' hM' ↦ cCodim_le_codimRepCanonical_of hMono d r hr M' hM')
    (fun p hp ↦ exists_kostantPartition_partitionIdeal_eq_of hMonoStrict d r hr p hp)

end DLNFibre.Core
