import DLNFibre.Core.CThetaQIPConverse

/-!
# `DLNFibre.Core.CCodimZeroMono` — dimension-monotonicity of `cCodim · 0`

The two combinatorial inequalities that discharge the gating hypotheses of the θ-count headline
(`Core.CCodimCornerMono.numTop_eq_ncard_topComponents_of_dimMono`):

* **`cCodim_zero_mono`** (weak): `e ≤ e'` pointwise ⟹ `cCodim e 0 ≤ cCodim e' 0`.
* **`cCodim_zero_strict`** (strict, all-vertex): `e < e'` at *every* vertex ⟹ `cCodim e 0 < cCodim e' 0`.

These are pure `CTheta`-level combinatorics over `ℤ` (no field, no geometry): statements about the
minimum of the quadratic `codimForm` over the corner-`0` Kostant partitions. The proof is the
**shortest-interval split**: `codimForm` is the type-A `Ext`-pairing form, and at an over-covered
vertex `k`, splitting the SHORTEST covering interval `[i,j]` into `[i,k−1] + [k+1,j]` never increases
`codimForm` — the split's `codimForm`-delta is `∑_Y coeff(Y) · m̄(Y)` over intervals `Y`, and every
`Y` with `coeff(Y) > 0` is a strictly-shorter covering interval of `k`, absent when `[i,j]` is the
shortest. Iterating reduces `e'` down to `e`.

This file reuses the bilinear `codimBil` machinery (`codimBil`, `codimForm_add`, biadditivity,
`extendℤ_nonneg`) from `Core.CThetaQIPConverse`.

**Dependency rule:** `Core` only — no `DLN`, no field; the inequalities are over `ℤ`.
-/

namespace DLNFibre.Core

open Finset

variable {N : ℕ}

/-! ## `codimBil (extendℤ m̄)` against a single interval box, as a `univ`-sum

For a partition `m̄ : Fin (N+1)² → ℕ`, pairing `extendℤ m̄` against the single-box indicator at
`(p, q)` (a `ℤ`-point) collapses to a sum over the `Fin²` interval grid:

* SECOND slot: `codimBil (extendℤ m̄) (box p q) = ∑_{Y} m̄ Y · 𝟙[y₁ ≤ p−1 ∧ p−1 ≤ y₂ ≤ q−1]`;
* FIRST slot: `codimBil (box p q) (extendℤ m̄) = ∑_{Y} m̄ Y · 𝟙[p+1 ≤ y₁ ≤ q+1 ∧ q+1 ≤ y₂]`.

Both hold for *all* `ℤ`-points `(p, q)` (when `p > q` the box is below-diagonal and the indicators
are unsatisfiable, so the sum is `0`, matching `codimBil` of the zero-on-box array). The `univ`-sum
form makes the split delta a single per-interval sum, where the sign argument is entrywise. -/

/-- The right-rectangle indicator: `Y = (y₁, y₂)` lies in the `codimBil · (box p q)` support iff the
box point is reachable (`1 ≤ p`, `q ≤ N`) and `y₁ ≤ p−1`, `p−1 ≤ y₂ ≤ q−1`. The reachability clamp
matches `codimBil`'s `u ≥ 1`, `v ≤ N` ranges (so the box `(p, q)` with `p < 1` or `q > N` is never
hit, giving `0`). -/
def rrInd (p q : ℤ) (Y : Fin (N + 1) × Fin (N + 1)) : Prop :=
  1 ≤ p ∧ q ≤ (N : ℤ) ∧ (Y.1 : ℤ) ≤ p - 1 ∧ p - 1 ≤ (Y.2 : ℤ) ∧ (Y.2 : ℤ) ≤ q - 1

/-- The left-rectangle indicator: `Y = (y₁, y₂)` lies in the `codimBil (box p q) ·` support iff the
box point is reachable (`0 ≤ p`, `q ≤ N−1`) and `p+1 ≤ y₁ ≤ q+1`, `q+1 ≤ y₂`. -/
def llInd (p q : ℤ) (Y : Fin (N + 1) × Fin (N + 1)) : Prop :=
  0 ≤ p ∧ q ≤ (N : ℤ) - 1 ∧ p + 1 ≤ (Y.1 : ℤ) ∧ (Y.1 : ℤ) ≤ q + 1 ∧ q + 1 ≤ (Y.2 : ℤ)

instance (p q : ℤ) (Y : Fin (N + 1) × Fin (N + 1)) : Decidable (rrInd p q Y) := by
  unfold rrInd; infer_instance

instance (p q : ℤ) (Y : Fin (N + 1) × Fin (N + 1)) : Decidable (llInd p q Y) := by
  unfold llInd; infer_instance

/-- The single-interval box indicator at `(p, q)` (as a `ℤ`-array), matching the shape used by
`Core.CThetaQIPConverse.codimBil_single_right`/`_left`. -/
def boxℤ (p q : ℤ) : ℤ → ℤ → ℤ := fun α β ↦ if α = p ∧ β = q then 1 else 0

/-- Reindex a rectangle `∑_{i∈Icc 1 p}∑_{j∈Icc p q} extendℤ m (i-1) (j-1)` (with `1 ≤ p ≤ q ≤ N`)
to the `univ`-filter form `∑_{Y : rrInd p q} m Y`, via `Y = (i-1, j-1)`. -/
theorem rect_right_eq_univ (m : Fin (N + 1) × Fin (N + 1) → ℕ) {p q : ℤ}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q ≤ (N : ℤ)) :
    (∑ i ∈ Finset.Icc (1 : ℤ) p, ∑ j ∈ Finset.Icc p q, extendℤ m (i - 1) (j - 1))
      = ∑ Y ∈ Finset.univ.filter (rrInd p q), (m Y : ℤ) := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij'
    (i := fun ij (hij : ij ∈ Finset.Icc (1 : ℤ) p ×ˢ Finset.Icc p q) ↦
      ((⟨(ij.1 - 1).toNat, by
          rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hij; omega⟩ : Fin (N + 1)),
       (⟨(ij.2 - 1).toNat, by
          rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hij; omega⟩ : Fin (N + 1))))
    (j := fun Y (_ : Y ∈ Finset.univ.filter (rrInd p q)) ↦
      (((Y.1 : ℤ) + 1, (Y.2 : ℤ) + 1) : ℤ × ℤ))
    ?_ ?_ ?_ ?_ ?_
  · -- forward map lands in the filter
    intro ij hij
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hij
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold rrInd
    simp only [Fin.val_mk]
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
    omega
  · -- inverse map lands in the product
    intro Y hY
    rw [Finset.mem_filter] at hY
    obtain ⟨-, hrr⟩ := hY
    obtain ⟨h1, h2, h3, h4, h5⟩ := hrr
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    dsimp only
    have := Y.1.isLt; have := Y.2.isLt
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · -- left inverse: (j ∘ i) = id on the product
    intro ij hij
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hij
    simp only [Fin.val_mk]
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
    ext <;> dsimp only <;> omega
  · -- right inverse: (i ∘ j) = id on the filter
    intro Y hY
    ext <;> simp
  · -- the summands match: `extendℤ m (i-1) (j-1) = m Y`
    intro ij hij
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hij
    rw [extendℤ_in_box m (by omega) (by omega) (by omega)]

/-- The `univ`-sum form of the right-rectangle for a partition. `m̄ Y` is summed over the intervals
`Y` with `rrInd p q Y`, against `extendℤ m̄`. -/
theorem codimBil_extendℤ_boxℤ_right (m : Fin (N + 1) × Fin (N + 1) → ℕ) (p q : ℤ) :
    codimBil N (extendℤ m) (boxℤ p q)
      = ∑ Y ∈ Finset.univ.filter (rrInd p q), (m Y : ℤ) := by
  by_cases hrange : 1 ≤ p ∧ p ≤ q ∧ q ≤ (N : ℤ)
  · obtain ⟨hp, hpq, hq⟩ := hrange
    rw [show boxℤ p q = (fun α β ↦ if α = p ∧ β = q then (1 : ℤ) else 0) from rfl,
      codimBil_single_right (extendℤ m) hp hpq hq, rect_right_eq_univ m hp hpq hq]
  · -- out of range: both sides are `0`.
    have hLHS : codimBil N (extendℤ m) (boxℤ p q) = 0 := by
      unfold codimBil boxℤ
      refine Finset.sum_eq_zero fun i hi ↦ Finset.sum_eq_zero fun u hu ↦
        Finset.sum_eq_zero fun j hj ↦ Finset.sum_eq_zero fun v hv ↦ ?_
      simp only [Finset.mem_Icc] at hi hu hj hv
      rw [if_neg (by rintro ⟨rfl, rfl⟩; exact hrange ⟨by omega, by omega, by omega⟩), mul_zero]
    have hRHS : Finset.univ.filter (rrInd p q)
        = (∅ : Finset (Fin (N + 1) × Fin (N + 1))) := by
      ext Y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      unfold rrInd; rintro ⟨h1, h2, h3, h4, h5⟩; exact hrange ⟨h1, by omega, h2⟩
    rw [hLHS, hRHS, Finset.sum_empty]

/-- Reindex the left-rectangle `∑_{u∈Icc (p+1) (q+1)}∑_{v∈Icc (q+1) N} extendℤ m u v` (with
`0 ≤ p ≤ q ≤ N`) to the `univ`-filter form `∑_{Y : llInd p q} m Y`, via `Y = (u, v)`. -/
theorem rect_left_eq_univ (m : Fin (N + 1) × Fin (N + 1) → ℕ) {p q : ℤ}
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ (N : ℤ)) :
    (∑ u ∈ Finset.Icc (p + 1) (q + 1), ∑ v ∈ Finset.Icc (q + 1) (N : ℤ), extendℤ m u v)
      = ∑ Y ∈ Finset.univ.filter (llInd p q), (m Y : ℤ) := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij'
    (i := fun uv (huv : uv ∈ Finset.Icc (p + 1) (q + 1) ×ˢ Finset.Icc (q + 1) (N : ℤ)) ↦
      ((⟨uv.1.toNat, by
          rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at huv; omega⟩ : Fin (N + 1)),
       (⟨uv.2.toNat, by
          rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at huv; omega⟩ : Fin (N + 1))))
    (j := fun Y (_ : Y ∈ Finset.univ.filter (llInd p q)) ↦ (((Y.1 : ℤ), (Y.2 : ℤ)) : ℤ × ℤ))
    ?_ ?_ ?_ ?_ ?_
  · intro uv huv
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at huv
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold llInd
    simp only [Fin.val_mk]
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
    omega
  · intro Y hY
    rw [Finset.mem_filter] at hY
    obtain ⟨-, hll⟩ := hY
    obtain ⟨h1, h2, h3, h4, h5⟩ := hll
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    dsimp only
    have := Y.1.isLt; have := Y.2.isLt
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · intro uv huv
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at huv
    simp only [Fin.val_mk]
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
  · intro Y hY
    ext <;> simp
  · intro uv huv
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at huv
    rw [extendℤ_in_box m (by omega) (by omega) (by omega)]

/-- The `univ`-sum form of the left-rectangle for a partition. -/
theorem codimBil_boxℤ_extendℤ_left (m : Fin (N + 1) × Fin (N + 1) → ℕ) (p q : ℤ) :
    codimBil N (boxℤ p q) (extendℤ m)
      = ∑ Y ∈ Finset.univ.filter (llInd p q), (m Y : ℤ) := by
  by_cases hrange : 0 ≤ p ∧ p ≤ q ∧ q ≤ (N : ℤ) - 1
  · obtain ⟨hp, hpq, hq⟩ := hrange
    rw [show boxℤ p q = (fun α β ↦ if α = p ∧ β = q then (1 : ℤ) else 0) from rfl,
      codimBil_single_left (extendℤ m) hp hpq (by omega), rect_left_eq_univ m hp hpq (by omega)]
  · -- out of range: both sides are `0`.
    have hLHS : codimBil N (boxℤ p q) (extendℤ m) = 0 := by
      unfold codimBil boxℤ
      refine Finset.sum_eq_zero fun i hi ↦ Finset.sum_eq_zero fun u hu ↦
        Finset.sum_eq_zero fun j hj ↦ Finset.sum_eq_zero fun v hv ↦ ?_
      simp only [Finset.mem_Icc] at hi hu hj hv
      rw [if_neg (by rintro ⟨rfl, rfl⟩; exact hrange ⟨by omega, by omega, by omega⟩), zero_mul]
    have hRHS : Finset.univ.filter (llInd p q)
        = (∅ : Finset (Fin (N + 1) × Fin (N + 1))) := by
      ext Y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      unfold llInd; rintro ⟨h1, h2, h3, h4, h5⟩; exact hrange ⟨h1, by omega, h2⟩
    rw [hLHS, hRHS, Finset.sum_empty]

/-! ## The interval split move `[a,d'] → [a,b] + [c,d']` (omitting the vertex `b+1 = c−1`)

`splitMove m a b c d'` (mirroring `Core.CThetaQIPConverse.concatMove` with a one-vertex gap `c = b+2`)
turns one copy of `[a,d']` into `[a,b]` and `[c,d']`, dropping coverage by `1` at the single vertex
`k = b+1 = c−1` and leaving every other vertex's coverage unchanged. The `codimForm`-change is the
split delta `boxℤ a b + boxℤ c d' − boxℤ a d'`; it is `≤ 0` when `[a,d']` is a *shortest* covering
interval of `k` with positive multiplicity. The endpoints `b, c` are honest `Fin (N+1)` values
(`b = k−1`, `c = k+1`), avoiding `Fin`-arithmetic in the definition; `c = b+2` is carried as a
hypothesis. -/

/-- The split move on the multiplicity array: `m(a,d') −= 1`, `m(a,b) += 1`, `m(c,d') += 1`. -/
def splitMove (m : Fin (N + 1) × Fin (N + 1) → ℕ) (a b c d' : Fin (N + 1)) :
    Fin (N + 1) × Fin (N + 1) → ℕ :=
  fun p ↦ m p + (if p = (a, b) then 1 else 0) + (if p = (c, d') then 1 else 0)
    - (if p = (a, d') then 1 else 0)

/-- The ℤ-delta of the split move: `+1` at `(a,b)`, `+1` at `(c,d')`, `−1` at `(a,d')`. -/
def splitDelta (a b c d' : Fin (N + 1)) : ℤ → ℤ → ℤ :=
  fun α β ↦ boxℤ (a : ℤ) (b : ℤ) α β + boxℤ (c : ℤ) (d' : ℤ) α β - boxℤ (a : ℤ) (d' : ℤ) α β

/-- **The `extendℤ`/delta connection.** Under the split preconditions (`a ≤ b`, `b < c`, `c ≤ d'`,
source `[a,d']` present), `extendℤ (splitMove m a b c d') = extendℤ m + splitDelta a b c d'`. The
three changed keys are distinct, so at each point at most one indicator fires and the ℕ-subtraction
is honest. -/
theorem extendℤ_splitMove {m : Fin (N + 1) × Fin (N + 1) → ℕ} {a b c d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbc : (b : ℕ) < c) (hcd : (c : ℕ) ≤ d')
    (hsad : 1 ≤ m (a, d')) :
    extendℤ (splitMove m a b c d') = extendℤ m + splitDelta a b c d' := by
  have hbd : (b : ℕ) ≠ d' := by omega
  have hac : (a : ℕ) ≠ c := by omega
  funext α β
  simp only [Pi.add_apply, extendℤ, splitDelta, boxℤ]
  by_cases hbox : (0 : ℤ) ≤ α ∧ α ≤ β ∧ β ≤ (N : ℤ)
  · rw [dif_pos hbox, dif_pos hbox]
    obtain ⟨hα0, hαβ, hβN⟩ := hbox
    set q : Fin (N + 1) × Fin (N + 1) := (⟨α.toNat, by omega⟩, ⟨β.toNat, by omega⟩) with hq
    have eAB : (q = (a, b)) ↔ (α = (a : ℤ) ∧ β = (b : ℤ)) := by
      rw [hq, Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]; dsimp only [Fin.val_mk]; omega
    have eCD : (q = (c, d')) ↔ (α = (c : ℤ) ∧ β = (d' : ℤ)) := by
      rw [hq, Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]; dsimp only [Fin.val_mk]; omega
    have eAD : (q = (a, d')) ↔ (α = (a : ℤ) ∧ β = (d' : ℤ)) := by
      rw [hq, Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]; dsimp only [Fin.val_mk]; omega
    rw [show splitMove m a b c d' (⟨α.toNat, by omega⟩, ⟨β.toNat, by omega⟩)
        = splitMove m a b c d' q from rfl, splitMove]
    have hba' : b ≠ d' := fun h ↦ hbd (by rw [h])
    have hca' : a ≠ c := fun h ↦ hac (by rw [h])
    by_cases h1 : q = (a, b)
    · have h2 : q ≠ (c, d') := by
        rw [h1]; simp only [ne_eq, Prod.mk.injEq, not_and]; exact fun h ↦ absurd h hca'
      have h3 : q ≠ (a, d') := by
        rw [h1]; simp only [ne_eq, Prod.mk.injEq, not_and]; exact fun _ ↦ hba'
      rw [if_pos h1, if_neg h2, if_neg h3, if_pos (eAB.mp h1),
        if_neg (fun h ↦ h2 (eCD.mpr h)), if_neg (fun h ↦ h3 (eAD.mpr h))]
      push_cast; ring
    · by_cases h2 : q = (c, d')
      · have h3 : q ≠ (a, d') := by
          rw [h2]; simp only [ne_eq, Prod.mk.injEq, not_and]; exact fun h ↦ absurd h hca'.symm
        rw [if_neg h1, if_pos h2, if_neg h3, if_neg (fun h ↦ h1 (eAB.mpr h)),
          if_pos (eCD.mp h2), if_neg (fun h ↦ h3 (eAD.mpr h))]
        push_cast; ring
      · by_cases h3 : q = (a, d')
        · rw [if_neg h1, if_neg h2, if_pos h3, if_neg (fun h ↦ h1 (eAB.mpr h)),
            if_neg (fun h ↦ h2 (eCD.mpr h)), if_pos (eAD.mp h3)]
          have hpos : 1 ≤ m q := by rw [h3]; exact hsad
          push_cast; omega
        · rw [if_neg h1, if_neg h2, if_neg h3, if_neg (fun h ↦ h1 (eAB.mpr h)),
            if_neg (fun h ↦ h2 (eCD.mpr h)), if_neg (fun h ↦ h3 (eAD.mpr h))]
          simp
  · simp only [dif_neg hbox]
    have haN : (a : ℤ) ≤ N := by have := a.isLt; omega
    have hdN : (d' : ℤ) ≤ N := by have := d'.isLt; omega
    rw [if_neg (by rintro ⟨h1, h2⟩; exact hbox ⟨by omega, by omega, by omega⟩),
      if_neg (by rintro ⟨h1, h2⟩; exact hbox ⟨by omega, by omega, by omega⟩),
      if_neg (by rintro ⟨h1, h2⟩; exact hbox ⟨by omega, by omega, by omega⟩)]
    ring

/-! ## The split delta as a single per-interval sum

`codimBil` is biadditive, so pairing `extendℤ m` against `splitDelta` (a ℤ-combination of three
boxes) and `splitDelta` against `extendℤ m` each expand into the three `univ`-sum rectangles. The
self term `codimForm (splitDelta)` vanishes. So the whole split-delta is one sum over intervals `Y`
of `m̄ Y · coeff Y`, where `coeff Y` is the indicator combination
`(rrInd_ab + rrInd_cd − rrInd_ad + llInd_ab + llInd_cd − llInd_ad) Y`. -/

/-- The per-interval coefficient of the split delta: the indicator combination over the three boxes
`[a,b]`, `[c,d']` (`+`) and `[a,d']` (`−`), in both the right- and left-rectangle slots. As an `ℤ`
(each indicator contributes `0`/`1`). -/
def splitCoeff (a b c d' : Fin (N + 1)) (Y : Fin (N + 1) × Fin (N + 1)) : ℤ :=
  ((if rrInd (a : ℤ) (b : ℤ) Y then 1 else 0)
      + (if rrInd (c : ℤ) (d' : ℤ) Y then 1 else 0) - (if rrInd (a : ℤ) (d' : ℤ) Y then 1 else 0))
  + ((if llInd (a : ℤ) (b : ℤ) Y then 1 else 0)
      + (if llInd (c : ℤ) (d' : ℤ) Y then 1 else 0) - (if llInd (a : ℤ) (d' : ℤ) Y then 1 else 0))

/-- `codimBil (extendℤ m) (splitDelta …)` as a `univ`-sum over intervals `Y` of `m̄ Y` weighted by
the right-rectangle indicator combination. -/
theorem codimBil_extendℤ_splitDelta_right (m : Fin (N + 1) × Fin (N + 1) → ℕ)
    (a b c d' : Fin (N + 1)) :
    codimBil N (extendℤ m) (splitDelta a b c d')
      = ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ)
          * ((if rrInd (a : ℤ) (b : ℤ) Y then 1 else 0)
              + (if rrInd (c : ℤ) (d' : ℤ) Y then 1 else 0)
              - (if rrInd (a : ℤ) (d' : ℤ) Y then 1 else 0)) := by
  have hbox : ∀ p q : ℤ, codimBil N (extendℤ m) (boxℤ p q)
      = ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * (if rrInd p q Y then 1 else 0) := by
    intro p q
    rw [codimBil_extendℤ_boxℤ_right, Finset.sum_filter]
    refine Finset.sum_congr rfl fun Y _ ↦ ?_
    split_ifs with h <;> simp
  rw [show splitDelta a b c d'
      = (boxℤ (a : ℤ) (b : ℤ) + boxℤ (c : ℤ) (d' : ℤ)) - boxℤ (a : ℤ) (d' : ℤ) by
        funext α β; simp only [Pi.sub_apply, Pi.add_apply]; rfl,
    codimBil_sub_right, codimBil_add_right, hbox, hbox, hbox, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun Y _ ↦ by ring

/-- `codimBil (splitDelta …) (extendℤ m)` as a `univ`-sum over intervals `Y` weighted by the
left-rectangle indicator combination. -/
theorem codimBil_splitDelta_extendℤ_left (m : Fin (N + 1) × Fin (N + 1) → ℕ)
    (a b c d' : Fin (N + 1)) :
    codimBil N (splitDelta a b c d') (extendℤ m)
      = ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ)
          * ((if llInd (a : ℤ) (b : ℤ) Y then 1 else 0)
              + (if llInd (c : ℤ) (d' : ℤ) Y then 1 else 0)
              - (if llInd (a : ℤ) (d' : ℤ) Y then 1 else 0)) := by
  have hbox : ∀ p q : ℤ, codimBil N (boxℤ p q) (extendℤ m)
      = ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * (if llInd p q Y then 1 else 0) := by
    intro p q
    rw [codimBil_boxℤ_extendℤ_left, Finset.sum_filter]
    refine Finset.sum_congr rfl fun Y _ ↦ ?_
    split_ifs with h <;> simp
  rw [show splitDelta a b c d'
      = (boxℤ (a : ℤ) (b : ℤ) + boxℤ (c : ℤ) (d' : ℤ)) - boxℤ (a : ℤ) (d' : ℤ) by
        funext α β; simp only [Pi.sub_apply, Pi.add_apply]; rfl,
    codimBil_sub_left, codimBil_add_left, hbox, hbox, hbox, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun Y _ ↦ by ring

/-- **The box-pairing value.** `codimBil (boxℤ p q) (boxℤ p' q')` is `1` exactly when the type-A
pairing fires (`0 ≤ p`, `q' ≤ N`, `p < p' ≤ q + 1`, `q < q'`), else `0`. Reduces to the right-rectangle
of `boxℤ p q` over the singleton support of `boxℤ p' q'` (via `codimBil_extendℤ_boxℤ_right`-style
collapse, here using the existing single-point collapse on the second box). -/
theorem codimBil_boxℤ_boxℤ (p q p' q' : ℤ) :
    codimBil N (boxℤ p q) (boxℤ p' q')
      = if 0 ≤ p ∧ q' ≤ (N : ℤ) ∧ p < p' ∧ p' ≤ q + 1 ∧ q < q' then 1 else 0 := by
  by_cases hp'r : 1 ≤ p' ∧ p' ≤ q' ∧ q' ≤ (N : ℤ)
  · obtain ⟨hp', hp'q', hq'⟩ := hp'r
    rw [show boxℤ p' q' = (fun α β ↦ if α = p' ∧ β = q' then (1 : ℤ) else 0) from rfl,
      codimBil_single_right (boxℤ p q) hp' hp'q' hq']
    -- `∑_{i∈[1,p']}∑_{j∈[p',q']} boxℤ p q (i-1) (j-1)` collapses at `(i,j)=(p+1,q+1)`.
    unfold boxℤ
    by_cases hcond : 0 ≤ p ∧ q' ≤ (N : ℤ) ∧ p < p' ∧ p' ≤ q + 1 ∧ q < q'
    · obtain ⟨hp, -, hpp, hpq, hqq⟩ := hcond
      rw [if_pos ⟨hp, hq', hpp, hpq, hqq⟩,
        Finset.sum_eq_single_of_mem (p + 1) (by simp only [Finset.mem_Icc]; omega),
        Finset.sum_eq_single_of_mem (q + 1) (by simp only [Finset.mem_Icc]; omega),
        if_pos ⟨by ring, by ring⟩]
      · intro j hj hjq; simp only [Finset.mem_Icc] at hj
        rw [if_neg (by rintro ⟨-, h⟩; exact hjq (by omega))]
      · intro i hi hip; simp only [Finset.mem_Icc] at hi
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        rw [if_neg (by rintro ⟨h, -⟩; exact hip (by omega))]
    · rw [if_neg hcond]
      refine Finset.sum_eq_zero fun i hi ↦ Finset.sum_eq_zero fun j hj ↦ ?_
      simp only [Finset.mem_Icc] at hi hj
      rw [if_neg (by rintro ⟨h1, h2⟩; exact hcond ⟨by omega, hq', by omega, by omega, by omega⟩)]
  · -- `p'` out of the single-point range: both sides `0`.
    rw [if_neg (by rintro ⟨hp0, hq', hpp, hpq, hqq⟩; exact hp'r ⟨by omega, by omega, hq'⟩)]
    unfold codimBil boxℤ
    refine Finset.sum_eq_zero fun i hi ↦ Finset.sum_eq_zero fun u hu ↦
      Finset.sum_eq_zero fun j hj ↦ Finset.sum_eq_zero fun v hv ↦ ?_
    simp only [Finset.mem_Icc] at hi hu hj hv
    -- the second factor (`boxℤ p' q' u v`) is `0`: `u = p', v = q'` would force `p'` in range
    rw [show (if (u : ℤ) = p' ∧ (v : ℤ) = q' then (1 : ℤ) else 0) = 0 from
      if_neg (by rintro ⟨h1, h2⟩; exact hp'r ⟨by omega, by omega, by omega⟩), mul_zero]

/-- **The split self-term vanishes (gap).** With the one-vertex gap `b + 1 < c`, no box-pair of
`splitDelta` is type-A adjacent, so `codimForm (splitDelta a b c d') = 0`. -/
theorem codimForm_splitDelta (a b c d' : Fin (N + 1)) (hab : (a : ℕ) ≤ b) (hbc : (b : ℕ) + 1 < c)
    (hcd : (c : ℕ) ≤ d') :
    codimForm N (splitDelta a b c d') = 0 := by
  have haN : (a : ℤ) ≤ N := by have := a.isLt; omega
  have hbN : (b : ℤ) ≤ N := by have := b.isLt; omega
  have hcN : (c : ℤ) ≤ N := by have := c.isLt; omega
  have hdN : (d' : ℤ) ≤ N := by have := d'.isLt; omega
  have habZ : (a : ℤ) ≤ b := by exact_mod_cast hab
  have hbcZ : (b : ℤ) + 1 < c := by exact_mod_cast hbc
  have hcdZ : (c : ℤ) ≤ d' := by exact_mod_cast hcd
  rw [show codimForm N (splitDelta a b c d') = codimBil N (splitDelta a b c d') (splitDelta a b c d')
      from rfl]
  rw [show splitDelta a b c d'
      = (boxℤ (a : ℤ) (b : ℤ) + boxℤ (c : ℤ) (d' : ℤ)) - boxℤ (a : ℤ) (d' : ℤ) by
        funext α β; simp only [Pi.sub_apply, Pi.add_apply]; rfl]
  simp only [codimBil_sub_left, codimBil_add_left, codimBil_sub_right, codimBil_add_right,
    codimBil_boxℤ_boxℤ]
  -- each of the nine box-pair indicators evaluates by `omega` on the endpoints (gap kills adjacency)
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  ring

/-! ## The split-`codimForm` delta as `∑_Y m̄ Y · splitCoeff Y` and its sign

Assembling the bilinear expansion: the split's `codimForm`-change is `∑_Y m̄ Y · splitCoeff Y`. Then
the sign lemma `splitCoeff_pos_imp` (`splitCoeff Y > 0 ⟹ Y covers k ∧ len Y < len I`) makes the
change `≤ 0` when `[a,d']` is a shortest covering interval of the omitted vertex `k = b+1`. -/

/-- **The split `codimForm`-delta.** With the gap `b + 1 < c` and source `[a,d']` present,
`codimForm (extendℤ (splitMove m a b c d')) = codimForm (extendℤ m) + ∑_Y m̄ Y · splitCoeff Y`. -/
theorem codimForm_splitMove (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a b c d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbc : (b : ℕ) + 1 < c) (hcd : (c : ℕ) ≤ d') (hsad : 1 ≤ m (a, d')) :
    codimForm N (extendℤ (splitMove m a b c d'))
      = codimForm N (extendℤ m)
        + ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * splitCoeff a b c d' Y := by
  rw [extendℤ_splitMove hab (by omega) hcd hsad, codimForm_add,
    codimBil_extendℤ_splitDelta_right, codimBil_splitDelta_extendℤ_left,
    codimForm_splitDelta a b c d' hab hbc hcd, add_zero, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun Y _ ↦ ?_
  unfold splitCoeff
  ring

/-- **The sign lemma (crux).** For the single-vertex-gap split `[a,d'] → [a,b] + [c,d']` with
`c = b + 2` (omitting vertex `k = b + 1`), any interval `Y` with `splitCoeff a b c d' Y > 0` covers
`k` (`Y.1 ≤ b + 1 ≤ Y.2`) and is strictly shorter than `[a,d']` (`Y.2 − Y.1 < d' − a`). The positive
contributions to the split delta are exactly the strictly-shorter covering intervals of `k`. -/
theorem splitCoeff_pos_imp {a b c d' : Fin (N + 1)} (hab : (a : ℕ) ≤ b) (hbc : (c : ℕ) = b + 2)
    (hcd : (c : ℕ) ≤ d') {Y : Fin (N + 1) × Fin (N + 1)} (hpos : 0 < splitCoeff a b c d' Y) :
    ((Y.1 : ℤ) ≤ (b : ℤ) + 1 ∧ (b : ℤ) + 1 ≤ (Y.2 : ℤ))
      ∧ (Y.2 : ℤ) - (Y.1 : ℤ) < (d' : ℤ) - (a : ℤ) := by
  -- pin all the integer endpoint relations omega needs (casts of `Fin` bounds + the move hyps)
  have hcZ : (c : ℤ) = (b : ℤ) + 2 := by exact_mod_cast hbc
  have habZ : (a : ℤ) ≤ b := by exact_mod_cast hab
  have hcdZ : (c : ℤ) ≤ d' := by exact_mod_cast hcd
  have hY1 : (Y.1 : ℤ) ≤ (N : ℤ) := by have := Y.1.isLt; omega
  have hY2 : (Y.2 : ℤ) ≤ (N : ℤ) := by have := Y.2.isLt; omega
  have haN : (a : ℤ) ≤ (N : ℤ) := by have := a.isLt; omega
  have hbN : (b : ℤ) ≤ (N : ℤ) := by have := b.isLt; omega
  have hdN : (d' : ℤ) ≤ (N : ℤ) := by have := d'.isLt; omega
  have hY1nn : (0 : ℤ) ≤ (Y.1 : ℤ) := by positivity
  have hY2nn : (0 : ℤ) ≤ (Y.2 : ℤ) := by positivity
  have hann : (0 : ℤ) ≤ (a : ℤ) := by positivity
  unfold splitCoeff rrInd llInd at hpos
  -- each indicator's condition is linear in the endpoints; `split_ifs` + `omega` discharges all cases
  split_ifs at hpos <;> omega

end DLNFibre.Core
