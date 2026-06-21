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

/-! ## The shortest-split does not increase `codimForm`

When `[a,d']` is a *shortest* covering interval of `k = b + 1` with positive multiplicity, every
interval `Y` with `splitCoeff Y > 0` is strictly shorter and covering, hence has multiplicity `0` (by
minimality). So `∑_Y m̄ Y · splitCoeff Y ≤ 0` and the split does not increase `codimForm`. -/

/-- **The shortest-split does not increase `codimForm`.** With the single-vertex-gap split
`[a,d'] → [a,b] + [c,d']` (`c = b + 2`, vertex `k = b + 1`), source present (`m (a,d') ≥ 1`), and
`[a,d']` a *shortest* covering interval of `k` among positive-multiplicity intervals
(`hshort`: any covering `Y` of positive multiplicity is at least as long), the split's
`codimForm`-change is `≤ 0`. -/
theorem codimForm_splitMove_le (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a b c d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbc : (c : ℕ) = b + 2) (hcd : (c : ℕ) ≤ d') (hsad : 1 ≤ m (a, d'))
    (hshort : ∀ Y : Fin (N + 1) × Fin (N + 1), 1 ≤ m Y →
      (Y.1 : ℤ) ≤ (b : ℤ) + 1 → (b : ℤ) + 1 ≤ (Y.2 : ℤ) →
      (d' : ℤ) - (a : ℤ) ≤ (Y.2 : ℤ) - (Y.1 : ℤ)) :
    codimForm N (extendℤ (splitMove m a b c d')) ≤ codimForm N (extendℤ m) := by
  rw [codimForm_splitMove m hab (by omega) hcd hsad]
  have hsum : ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * splitCoeff a b c d' Y ≤ 0 := by
    refine Finset.sum_nonpos fun Y _ ↦ ?_
    rcases lt_or_ge 0 (splitCoeff a b c d' Y) with hc | hc
    · -- `splitCoeff Y > 0`: `Y` covers `k` and is strictly shorter ⟹ `m Y = 0` by minimality
      obtain ⟨⟨h1, h2⟩, hlen⟩ := splitCoeff_pos_imp hab hbc hcd hc
      have hmY : m Y = 0 := by
        by_contra hne
        exact absurd (hshort Y (Nat.one_le_iff_ne_zero.mpr hne) h1 h2) (not_le.mpr hlen)
      rw [hmY]; simp
    · exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hc
  linarith

/-! ## The shortest-split lands in the corner-`0` Kostant partitions of the decremented vector

The split changes coverage by `−1` at the omitted vertex `k = b + 1` and by `0` elsewhere, so it
carries a corner-`0` Kostant partition of `e'` to one of `e''` (= `e'` with `e' k` decremented),
provided the source `[a,d']` is present and `[a,d'] ≠ [0,N]` (corner stays `0`). -/

/-- **Filtered-coverage change of the split move** (as `ℤ`). At every vertex `v`, the coverage of
`splitMove m a b c d'` is the coverage of `m` plus the indicator of `[a,b]` covering `v`, plus that of
`[c,d']`, minus that of `[a,d']`. -/
theorem splitMove_cover (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a b c d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbc : (c : ℕ) = b + 2) (hcd : (c : ℕ) ≤ d') (hsad : 1 ≤ m (a, d'))
    (v : Fin (N + 1)) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
        splitMove m a b c d' p : ℤ)
      = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2), m p : ℤ)
        + (if a ≤ v ∧ v ≤ b then 1 else 0) + (if c ≤ v ∧ v ≤ d' then 1 else 0)
        - (if a ≤ v ∧ v ≤ d' then 1 else 0) := by
  set S := Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2) with hS
  have hterm : ∀ p : Fin (N + 1) × Fin (N + 1),
      ((splitMove m a b c d' p : ℕ) : ℤ)
        = (m p : ℤ) + (if p = (a, b) then 1 else 0) + (if p = (c, d') then 1 else 0)
          - (if p = (a, d') then 1 else 0) := by
    intro p
    have hac : a ≠ c := by rw [Fin.ne_iff_vne]; omega
    have hbd : b ≠ d' := by rw [Fin.ne_iff_vne]; omega
    by_cases h1 : p = (a, b)
    · have h2 : p ≠ (c, d') := by
        rw [h1]; intro h; exact hac (congrArg Prod.fst h)
      have h3 : p ≠ (a, d') := by
        rw [h1]; intro h; exact hbd (congrArg Prod.snd h)
      simp only [splitMove, if_pos h1, if_neg h2, if_neg h3, Nat.add_zero, Nat.sub_zero]
      push_cast; ring
    · by_cases h2 : p = (c, d')
      · have h3 : p ≠ (a, d') := by
          rw [h2]; intro h; exact hac (congrArg Prod.fst h).symm
        simp only [splitMove, if_pos h2, if_neg h1, if_neg h3, Nat.add_zero, Nat.sub_zero]
        push_cast; ring
      · by_cases h3 : p = (a, d')
        · have hpos : 1 ≤ m p := by rw [h3]; exact hsad
          simp only [splitMove, if_pos h3, if_neg h1, if_neg h2, Nat.add_zero]
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        · simp only [splitMove, if_neg h1, if_neg h2, if_neg h3, Nat.add_zero, Nat.sub_zero]
          push_cast; ring
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ S) ↦ hterm p),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' S (a, b), Finset.sum_ite_eq' S (c, d'), Finset.sum_ite_eq' S (a, d')]
  have hmemS : ∀ x y : Fin (N + 1), ((x, y) ∈ S) ↔ (x ≤ v ∧ v ≤ y) := by
    intro x y; rw [hS]; simp [Finset.mem_filter]
  simp only [hmemS]

/-- **The shortest-split lands in the corner-`0` Kostant partitions of the decremented vector.** If
`m` is a corner-`0` Kostant partition of `e'`, `[a,d']` covers `k` (with `(k : ℕ) = b + 1`,
`c = b + 2`), is present (`m (a,d') ≥ 1`), and is not the all-covering `[0,N]` (so the corner stays
`0`), then `splitMove m a b c d'` is a corner-`0` Kostant partition of `e''` — `e'` with the coverage
at `k` decremented by `1` (`e'' = Function.update e' k (e' k - 1)`). -/
theorem splitMove_mem {e' : Fin (N + 1) → ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    {a b c d' k : Fin (N + 1)} (hm : m ∈ kostantPartitions e' 0)
    (hab : (a : ℕ) ≤ b) (hbc : (c : ℕ) = b + 2) (hcd : (c : ℕ) ≤ d') (hk : (k : ℕ) = b + 1)
    (hsad : 1 ≤ m (a, d')) (hcorner : (a, d') ≠ ((0 : Fin (N + 1)), Fin.last N)) :
    splitMove m a b c d' ∈ kostantPartitions (Function.update e' k (e' k - 1)) 0 := by
  obtain ⟨hbnd, hsupp, hkost, hc0⟩ := mem_kostantPartitions.mp hm
  -- coverage of `[a,d']` at `k`: `a ≤ k ≤ d'` (since `a ≤ b < k = b+1 ≤ c ≤ d'`)
  have hak : a ≤ k := Fin.le_def.mpr (by omega)
  have hkd : k ≤ d' := Fin.le_def.mpr (by omega)
  have hsupp' : ∀ p, ¬ p.1 ≤ p.2 → splitMove m a b c d' p = 0 := by
    intro p hp
    have h1 : p ≠ (a, b) := fun h ↦ hp (by rw [h]; exact hab)
    have h2 : p ≠ (c, d') := fun h ↦ hp (by rw [h]; exact (Fin.le_def.mpr hcd))
    have h3 : p ≠ (a, d') := fun h ↦ hp (by rw [h]; exact (Fin.le_def.mpr (by omega : (a : ℕ) ≤ d')))
    simp only [splitMove, if_neg h1, if_neg h2, if_neg h3, Nat.add_zero, Nat.sub_zero]
    exact hsupp p hp
  -- `e' k ≥ 1`: `[a,d']` covers `k` and has multiplicity `≥ 1`, so it is one summand of `e' k`.
  have hekpos : 1 ≤ e' k := by
    rw [hkost k]
    refine le_trans hsad (Finset.single_le_sum (fun q _ ↦ Nat.zero_le _) ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hak, hkd⟩
  -- Kostant at every vertex: read the coverage shift off `splitMove_cover`
  have hkost' : ∀ v, kostantAt (Function.update e' k (e' k - 1)) (splitMove m a b c d') v := by
    intro v
    rw [kostantAt]
    have hcov := splitMove_cover m hab hbc hcd hsad v
    have hbase : (e' v : ℤ)
        = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
            m p : ℤ) := by exact_mod_cast hkost v
    -- coverage delta at `v`: `−1` if `v = k`, else `0`
    have hZ : ((Function.update e' k (e' k - 1) v : ℕ) : ℤ)
        = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
            splitMove m a b c d' p : ℤ) := by
      rw [hcov, ← hbase]
      -- the `e' k − 1` decrement value, as a ℤ subtraction (honest since `e' k ≥ 1`)
      have hupd : ((Function.update e' k (e' k - 1) v : ℕ) : ℤ)
          = (e' v : ℤ) - (if v = k then 1 else 0) := by
        by_cases hvk : v = k
        · subst hvk; rw [Function.update_self, if_pos rfl, Nat.cast_sub hekpos]; push_cast; ring
        · rw [Function.update_of_ne hvk, if_neg hvk]; ring
      rw [hupd]
      -- normalise the `Fin`-interval conditions and the decrement to `ℕ`/`v = k`, then `omega`
      have hvkN : (v = k) ↔ ((v : ℕ) = b + 1) := by rw [Fin.ext_iff]; omega
      simp only [Fin.le_def, hvkN]
      split_ifs <;> omega
    exact_mod_cast hZ
  refine mem_kostantPartitions.mpr ⟨?_, hsupp', hkost', ?_⟩
  · exact bound_of_kostant hsupp' hkost'
  · -- corner `(0, last)`: all three split keys differ from it, so it keeps `m (0,last) = 0`
    have hdN : (d' : ℕ) ≤ N := by have := d'.isLt; omega
    have h1 : ((0 : Fin (N + 1)), Fin.last N) ≠ (a, b) := by
      intro hh; rw [Prod.mk.injEq] at hh; have := hh.2
      rw [Fin.ext_iff, Fin.val_last] at this; omega
    have h2 : ((0 : Fin (N + 1)), Fin.last N) ≠ (c, d') := by
      intro hh; rw [Prod.mk.injEq] at hh; have := hh.1
      rw [Fin.ext_iff, Fin.val_zero] at this; omega
    have h3 : ((0 : Fin (N + 1)), Fin.last N) ≠ (a, d') := fun h ↦ hcorner h.symm
    show splitMove m a b c d' ((0 : Fin (N + 1)), Fin.last N) = 0
    simp only [splitMove, if_neg h1, if_neg h2, if_neg h3, Nat.add_zero, Nat.sub_zero]
    exact hc0

/-! ## The reduction: every corner-`0` partition of `e'` dominates one of `e` (for `e ≤ e'`)

The shortest-split step packaged for induction. At an over-covered vertex `k`, the shortest covering
interval `[a,d']` (positive multiplicity) is split — generically into `[a,k−1] + [k+1,d']`, with the
left piece dropped when `k = a` and the right piece dropped when `k = d'` (a single endpoint or a
singleton). This `splitStep` is the uniform move; reusing the interior `splitMove` machinery requires
both pieces present, so the endpoint/singleton cases are handled by the same bilinear delta with the
empty box contributing `0`. The recursion on `∑ e'` then drives `e'` down to `e`. -/

/-- Among the positive-multiplicity intervals of `m` covering a vertex `k`, there is one of minimal
length, *provided at least one exists*. Extracts `[a,d']` with `m (a,d') ≥ 1`, `a ≤ k ≤ d'`, and
minimality: any covering positive-multiplicity `Y` is at least as long. -/
theorem exists_shortest_covering {m : Fin (N + 1) × Fin (N + 1) → ℕ} {k : Fin (N + 1)}
    (hcov : ∃ p : Fin (N + 1) × Fin (N + 1), 1 ≤ m p ∧ p.1 ≤ k ∧ k ≤ p.2) :
    ∃ p : Fin (N + 1) × Fin (N + 1), (1 ≤ m p ∧ p.1 ≤ k ∧ k ≤ p.2) ∧
      ∀ q : Fin (N + 1) × Fin (N + 1), 1 ≤ m q → q.1 ≤ k → k ≤ q.2 →
        (p.2 : ℤ) - (p.1 : ℤ) ≤ (q.2 : ℤ) - (q.1 : ℤ) := by
  classical
  -- the covering positive-multiplicity intervals form a nonempty finite set; take a length-minimiser
  set T : Finset (Fin (N + 1) × Fin (N + 1)) :=
    Finset.univ.filter (fun p ↦ 1 ≤ m p ∧ p.1 ≤ k ∧ k ≤ p.2) with hT
  have hTne : T.Nonempty := by
    obtain ⟨p, hp⟩ := hcov; exact ⟨p, by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hp⟩⟩
  obtain ⟨p, hpT, hpmin⟩ := T.exists_min_image (fun p ↦ (p.2 : ℤ) - (p.1 : ℤ)) hTne
  rw [hT, Finset.mem_filter] at hpT
  refine ⟨p, hpT.2, fun q hq hq1 hq2 ↦ ?_⟩
  exact hpmin q (by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hq, hq1, hq2⟩)

/-- The guarded reduction move: replace one copy of `[a,d']` by `[a,b]` (only when `a ≤ b`) and
`[c,d']` (only when `c ≤ d'`). With `b = k−1`, `c = k+1` this is the shortest-split, dropping the
left piece at `k = a` and the right piece at `k = d'`, so a single uniform move covers the interior,
endpoint and singleton cases. -/
def redMove (m : Fin (N + 1) × Fin (N + 1) → ℕ) (a b c d' : Fin (N + 1)) :
    Fin (N + 1) × Fin (N + 1) → ℕ :=
  fun p ↦ m p + (if a ≤ b ∧ p = (a, b) then 1 else 0) + (if c ≤ d' ∧ p = (c, d') then 1 else 0)
    - (if p = (a, d') then 1 else 0)

/-- `codimForm` reads its argument only at box points `(i-1, j-1)` and `(u, v)` with
`1 ≤ i ≤ u ≤ j ≤ v ≤ N` (so first index `≤` second, both in `[0, N]`). Hence two ℤ-arrays agreeing on
the box `{(α,β) : 0 ≤ α ≤ β ≤ N}` have equal `codimForm`. -/
theorem codimForm_congr_onbox {f g : ℤ → ℤ → ℤ}
    (h : ∀ α β : ℤ, 0 ≤ α → α ≤ β → β ≤ (N : ℤ) → f α β = g α β) :
    codimForm N f = codimForm N g := by
  unfold codimForm
  refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun u hu ↦
    Finset.sum_congr rfl fun j hj ↦ Finset.sum_congr rfl fun v hv ↦ ?_
  rw [Finset.mem_Icc] at hi hu hj hv
  rw [h (i - 1) (j - 1) (by omega) (by omega) (by omega), h u v (by omega) (by omega) (by omega)]

/-- `redMove` and `splitMove` have the same `extendℤ` *on the box*: there the guards `a ≤ b` /
`c ≤ d'` are automatic (a box-point `(a,b)` has `a ≤ b`). Off the box `codimForm` does not read them,
so `codimForm` of the two agree. -/
theorem extendℤ_redMove_onbox (m : Fin (N + 1) × Fin (N + 1) → ℕ) (a b c d' : Fin (N + 1))
    {α β : ℤ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ (N : ℤ)) :
    extendℤ (redMove m a b c d') α β = extendℤ (splitMove m a b c d') α β := by
  unfold extendℤ
  rw [dif_pos ⟨hα, hαβ, hβ⟩, dif_pos ⟨hα, hαβ, hβ⟩]
  congr 1
  set q : Fin (N + 1) × Fin (N + 1) := (⟨α.toNat, by omega⟩, ⟨β.toNat, by omega⟩) with hq
  show redMove m a b c d' q = splitMove m a b c d' q
  have hαβN : (q.1 : ℕ) ≤ q.2 := by rw [hq]; dsimp only [Fin.val_mk]; omega
  simp only [redMove, splitMove]
  -- the guards `a ≤ b` / `c ≤ d'` are redundant on-box (only fire when `q` equals an on-box key)
  have gAB : (if a ≤ b ∧ q = (a, b) then (1 : ℕ) else 0) = (if q = (a, b) then 1 else 0) := by
    by_cases h : q = (a, b)
    · rw [if_pos ⟨by rw [h] at hαβN; exact hαβN, h⟩, if_pos h]
    · rw [if_neg (fun hh ↦ h hh.2), if_neg h]
  have gCD : (if c ≤ d' ∧ q = (c, d') then (1 : ℕ) else 0) = (if q = (c, d') then 1 else 0) := by
    by_cases h : q = (c, d')
    · rw [if_pos ⟨by rw [h] at hαβN; exact hαβN, h⟩, if_pos h]
    · rw [if_neg (fun hh ↦ h hh.2), if_neg h]
  rw [gAB, gCD]

/-- **`redMove` `codimForm`-delta.** For `a ≤ b`, `b + 1 < c`, `c ≤ d'`, source present, the guarded
`redMove` has the same `codimForm`-delta as the interior `splitMove`:
`codimForm (extendℤ (redMove …)) = codimForm (extendℤ m) + ∑_Y m̄ Y · splitCoeff Y`. The guards differ
from `splitMove` only off the box, which `codimForm` never reads (`codimForm_congr_onbox`). -/
theorem codimForm_redMove (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a b c d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbc : (b : ℕ) + 1 < c) (hcd : (c : ℕ) ≤ d') (hsad : 1 ≤ m (a, d')) :
    codimForm N (extendℤ (redMove m a b c d'))
      = codimForm N (extendℤ m)
        + ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * splitCoeff a b c d' Y := by
  rw [codimForm_congr_onbox (fun α β hα hαβ hβ ↦ extendℤ_redMove_onbox m a b c d' hα hαβ hβ),
    codimForm_splitMove m hab hbc hcd hsad]

/-- **`redMove` does not increase `codimForm`** when `[a,d']` is a shortest covering interval of
`k = b + 1` (`c = b + 2`) of positive multiplicity. Same sign argument as `codimForm_splitMove_le`,
now uniform over the interior, endpoint and singleton cases. -/
theorem codimForm_redMove_le (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a b c d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbc : (c : ℕ) = b + 2) (hcd : (c : ℕ) ≤ d') (hsad : 1 ≤ m (a, d'))
    (hshort : ∀ Y : Fin (N + 1) × Fin (N + 1), 1 ≤ m Y →
      (Y.1 : ℤ) ≤ (b : ℤ) + 1 → (b : ℤ) + 1 ≤ (Y.2 : ℤ) →
      (d' : ℤ) - (a : ℤ) ≤ (Y.2 : ℤ) - (Y.1 : ℤ)) :
    codimForm N (extendℤ (redMove m a b c d')) ≤ codimForm N (extendℤ m) := by
  rw [codimForm_redMove m hab (by omega) hcd hsad]
  have hsum : ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * splitCoeff a b c d' Y ≤ 0 := by
    refine Finset.sum_nonpos fun Y _ ↦ ?_
    rcases lt_or_ge 0 (splitCoeff a b c d' Y) with hc | hc
    · obtain ⟨⟨h1, h2⟩, hlen⟩ := splitCoeff_pos_imp hab hbc hcd hc
      have hmY : m Y = 0 := by
        by_contra hne
        exact absurd (hshort Y (Nat.one_le_iff_ne_zero.mpr hne) h1 h2) (not_le.mpr hlen)
      rw [hmY]; simp
    · exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hc
  linarith

/-- **Filtered-coverage change of `redMove`** (as `ℤ`). At every vertex `v`, the coverage of
`redMove m a b c d'` is the coverage of `m` plus the *guarded* `[a,b]`/`[c,d']` indicators, minus the
`[a,d']` indicator. -/
theorem redMove_cover (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a b c d' : Fin (N + 1)}
    (hac0 : (a : ℕ) < c) (hbc : (c : ℕ) = b + 2) (hcd : (c : ℕ) ≤ d') (hsad : 1 ≤ m (a, d'))
    (v : Fin (N + 1)) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
        redMove m a b c d' p : ℤ)
      = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2), m p : ℤ)
        + (if a ≤ b ∧ a ≤ v ∧ v ≤ b then 1 else 0) + (if c ≤ d' ∧ c ≤ v ∧ v ≤ d' then 1 else 0)
        - (if a ≤ v ∧ v ≤ d' then 1 else 0) := by
  set S := Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2) with hS
  have hac : a ≠ c := by rw [Fin.ne_iff_vne]; omega
  have hbd : b ≠ d' := by rw [Fin.ne_iff_vne]; omega
  have hterm : ∀ p : Fin (N + 1) × Fin (N + 1),
      ((redMove m a b c d' p : ℕ) : ℤ)
        = (m p : ℤ) + (if a ≤ b ∧ p = (a, b) then 1 else 0) + (if c ≤ d' ∧ p = (c, d') then 1 else 0)
          - (if p = (a, d') then 1 else 0) := by
    intro p
    by_cases h1 : a ≤ b ∧ p = (a, b)
    · have h2 : ¬ (c ≤ d' ∧ p = (c, d')) := by
        rintro ⟨-, h⟩; rw [h1.2] at h; exact hac (congrArg Prod.fst h)
      have h3 : p ≠ (a, d') := by rw [h1.2]; intro h; exact hbd (congrArg Prod.snd h)
      simp only [redMove, if_pos h1, if_neg h2, if_neg h3, Nat.add_zero, Nat.sub_zero]
      push_cast; ring
    · by_cases h2 : c ≤ d' ∧ p = (c, d')
      · have h3 : p ≠ (a, d') := by rw [h2.2]; intro h; exact hac (congrArg Prod.fst h).symm
        simp only [redMove, if_neg h1, if_pos h2, if_neg h3, Nat.add_zero, Nat.sub_zero]
        push_cast; ring
      · by_cases h3 : p = (a, d')
        · have hpos : 1 ≤ m p := by rw [h3]; exact hsad
          simp only [redMove, if_neg h1, if_neg h2, if_pos h3, Nat.add_zero]
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        · simp only [redMove, if_neg h1, if_neg h2, if_neg h3, Nat.add_zero, Nat.sub_zero]
          push_cast; ring
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ S) ↦ hterm p),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- collapse each guarded single-key indicator sum
  have hcollapse : ∀ (P : Prop) [Decidable P] (key : Fin (N + 1) × Fin (N + 1)),
      (∑ p ∈ S, if P ∧ p = key then (1 : ℤ) else 0)
        = if P ∧ key ∈ S then 1 else 0 := by
    intro P _ key
    by_cases hP : P
    · simp only [hP, true_and]; rw [Finset.sum_ite_eq' S key]
    · simp only [hP, false_and, if_false, Finset.sum_const_zero]
  rw [hcollapse (a ≤ b) (a, b), hcollapse (c ≤ d') (c, d'), Finset.sum_ite_eq' S (a, d')]
  have hmemS : ∀ x y : Fin (N + 1), ((x, y) ∈ S) ↔ (x ≤ v ∧ v ≤ y) := by
    intro x y; rw [hS]; simp [Finset.mem_filter]
  simp only [hmemS]

/-- **The shortest `redMove` lands in the corner-`0` Kostant partitions of the decremented vector.**
Uniform over interior, endpoint and singleton: if `m ∈ kostantPartitions e' 0`, `[a,d']` covers `k`
(`(k:ℕ) = b + 1`, `c = b + 2`, `a ≤ k ≤ d'`), is present, and `[a,d'] ≠ [0,N]`, then `redMove m a b c
d' ∈ kostantPartitions (Function.update e' k (e' k - 1)) 0`. -/
theorem redMove_mem {e' : Fin (N + 1) → ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    {a b c d' k : Fin (N + 1)} (hm : m ∈ kostantPartitions e' 0)
    (hak : a ≤ k) (hkd : k ≤ d') (hbc : (c : ℕ) = b + 2) (hcd : (c : ℕ) ≤ d') (hk : (k : ℕ) = b + 1)
    (hsad : 1 ≤ m (a, d')) (hcorner : (a, d') ≠ ((0 : Fin (N + 1)), Fin.last N)) :
    redMove m a b c d' ∈ kostantPartitions (Function.update e' k (e' k - 1)) 0 := by
  obtain ⟨hbnd, hsupp, hkost, hc0⟩ := mem_kostantPartitions.mp hm
  have hakN : (a : ℕ) ≤ k := Fin.le_def.mp hak
  have hkdN : (k : ℕ) ≤ d' := Fin.le_def.mp hkd
  have hac0 : (a : ℕ) < c := by omega
  -- support: off the triangle, all three guarded keys differ, so `redMove m p = m p = 0`
  have hsupp' : ∀ p, ¬ p.1 ≤ p.2 → redMove m a b c d' p = 0 := by
    intro p hp
    have h1 : ¬ (a ≤ b ∧ p = (a, b)) := fun h ↦ hp (by rw [h.2]; exact h.1)
    have h2 : ¬ (c ≤ d' ∧ p = (c, d')) := fun h ↦ hp (by rw [h.2]; exact (Fin.le_def.mpr hcd))
    have h3 : p ≠ (a, d') := fun h ↦ hp (by rw [h]; exact (Fin.le_def.mpr (by omega : (a : ℕ) ≤ d')))
    simp only [redMove, if_neg h1, if_neg h2, if_neg h3, Nat.add_zero, Nat.sub_zero]
    exact hsupp p hp
  have hekpos : 1 ≤ e' k := by
    rw [hkost k]
    refine le_trans hsad (Finset.single_le_sum (fun q _ ↦ Nat.zero_le _) ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hak, hkd⟩
  have hkost' : ∀ v, kostantAt (Function.update e' k (e' k - 1)) (redMove m a b c d') v := by
    intro v
    rw [kostantAt]
    have hcov := redMove_cover m hac0 hbc hcd hsad v
    have hbase : (e' v : ℤ)
        = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
            m p : ℤ) := by exact_mod_cast hkost v
    have hZ : ((Function.update e' k (e' k - 1) v : ℕ) : ℤ)
        = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
            redMove m a b c d' p : ℤ) := by
      rw [hcov, ← hbase]
      have hupd : ((Function.update e' k (e' k - 1) v : ℕ) : ℤ)
          = (e' v : ℤ) - (if v = k then 1 else 0) := by
        by_cases hvk : v = k
        · subst hvk; rw [Function.update_self, if_pos rfl, Nat.cast_sub hekpos]; push_cast; ring
        · rw [Function.update_of_ne hvk, if_neg hvk]; ring
      rw [hupd]
      have hvkN : (v = k) ↔ ((v : ℕ) = b + 1) := by rw [Fin.ext_iff]; omega
      simp only [Fin.le_def, hvkN]
      split_ifs <;> omega
    exact_mod_cast hZ
  refine mem_kostantPartitions.mpr ⟨bound_of_kostant hsupp' hkost', hsupp', hkost', ?_⟩
  · have hdN : (d' : ℕ) ≤ N := by have := d'.isLt; omega
    have h1 : ¬ (a ≤ b ∧ ((0 : Fin (N + 1)), Fin.last N) = (a, b)) := by
      rintro ⟨-, hh⟩; rw [Prod.mk.injEq] at hh; have := hh.2
      rw [Fin.ext_iff, Fin.val_last] at this; omega
    have h2 : ¬ (c ≤ d' ∧ ((0 : Fin (N + 1)), Fin.last N) = (c, d')) := by
      rintro ⟨-, hh⟩; rw [Prod.mk.injEq] at hh; have := hh.1
      rw [Fin.ext_iff, Fin.val_zero] at this; omega
    have h3 : ((0 : Fin (N + 1)), Fin.last N) ≠ (a, d') := fun h ↦ hcorner h.symm
    show redMove m a b c d' ((0 : Fin (N + 1)), Fin.last N) = 0
    simp only [redMove, if_neg h1, if_neg h2, if_neg h3, Nat.add_zero, Nat.sub_zero]
    exact hc0

/-! ## The boundary shrink moves (omitting an endpoint of `[a,d']`)

When the omitted vertex `k` is an endpoint of `[a,d']` (so the interior split's left or right piece is
not just empty but unrepresentable — e.g. `k = a = 0`), use a single-piece shrink: `leftShrink`
replaces `[a,d']` by `[c,d']` (`c = a+1`, omitting vertex `a`); `rightShrink` replaces it by `[a,b]`
(`b = d'−1`, omitting vertex `d'`). Each reuses the same `boxℤ` `codimForm` machinery (one fewer
piece than `redMove`). -/

/-- The left-shrink move: replace one copy of `[a,d']` by `[c,d']` (kept only when `c ≤ d'`),
omitting the left endpoint `a` (`c = a+1`). -/
def leftShrink (m : Fin (N + 1) × Fin (N + 1) → ℕ) (a c d' : Fin (N + 1)) :
    Fin (N + 1) × Fin (N + 1) → ℕ :=
  fun p ↦ m p + (if c ≤ d' ∧ p = (c, d') then 1 else 0) - (if p = (a, d') then 1 else 0)

/-- The left-shrink ℤ-delta: `boxℤ c d' − boxℤ a d'`. -/
def leftDelta (a c d' : Fin (N + 1)) : ℤ → ℤ → ℤ :=
  fun α β ↦ boxℤ (c : ℤ) (d' : ℤ) α β - boxℤ (a : ℤ) (d' : ℤ) α β

/-- Per-interval coefficient of the left-shrink delta. -/
def leftCoeff (a c d' : Fin (N + 1)) (Y : Fin (N + 1) × Fin (N + 1)) : ℤ :=
  ((if rrInd (c : ℤ) (d' : ℤ) Y then 1 else 0) - (if rrInd (a : ℤ) (d' : ℤ) Y then 1 else 0))
  + ((if llInd (c : ℤ) (d' : ℤ) Y then 1 else 0) - (if llInd (a : ℤ) (d' : ℤ) Y then 1 else 0))

/-- `codimBil (extendℤ m) (leftDelta …)` as a per-interval `univ`-sum (right-rectangle indicators). -/
theorem codimBil_extendℤ_leftDelta_right (m : Fin (N + 1) × Fin (N + 1) → ℕ) (a c d' : Fin (N + 1)) :
    codimBil N (extendℤ m) (leftDelta a c d')
      = ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ)
          * ((if rrInd (c : ℤ) (d' : ℤ) Y then 1 else 0)
              - (if rrInd (a : ℤ) (d' : ℤ) Y then 1 else 0)) := by
  have hbox : ∀ p q : ℤ, codimBil N (extendℤ m) (boxℤ p q)
      = ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * (if rrInd p q Y then 1 else 0) := by
    intro p q
    rw [codimBil_extendℤ_boxℤ_right, Finset.sum_filter]
    exact Finset.sum_congr rfl fun Y _ ↦ by split_ifs with h <;> simp
  rw [show leftDelta a c d' = boxℤ (c : ℤ) (d' : ℤ) - boxℤ (a : ℤ) (d' : ℤ) by
        funext α β; simp only [Pi.sub_apply]; rfl,
    codimBil_sub_right, hbox, hbox, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun Y _ ↦ by ring

/-- `codimBil (leftDelta …) (extendℤ m)` as a per-interval `univ`-sum (left-rectangle indicators). -/
theorem codimBil_leftDelta_extendℤ_left (m : Fin (N + 1) × Fin (N + 1) → ℕ) (a c d' : Fin (N + 1)) :
    codimBil N (leftDelta a c d') (extendℤ m)
      = ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ)
          * ((if llInd (c : ℤ) (d' : ℤ) Y then 1 else 0)
              - (if llInd (a : ℤ) (d' : ℤ) Y then 1 else 0)) := by
  have hbox : ∀ p q : ℤ, codimBil N (boxℤ p q) (extendℤ m)
      = ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * (if llInd p q Y then 1 else 0) := by
    intro p q
    rw [codimBil_boxℤ_extendℤ_left, Finset.sum_filter]
    exact Finset.sum_congr rfl fun Y _ ↦ by split_ifs with h <;> simp
  rw [show leftDelta a c d' = boxℤ (c : ℤ) (d' : ℤ) - boxℤ (a : ℤ) (d' : ℤ) by
        funext α β; simp only [Pi.sub_apply]; rfl,
    codimBil_sub_left, hbox, hbox, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun Y _ ↦ by ring

/-- The left-shrink self-term `codimForm (leftDelta …) = 0` (two boxes that never type-A pair when
`a < c ≤ d'`). -/
theorem codimForm_leftDelta (a c d' : Fin (N + 1)) (hac : (a : ℕ) < c) (hcd : (c : ℕ) ≤ d') :
    codimForm N (leftDelta a c d') = 0 := by
  have hcN : (c : ℤ) ≤ N := by have := c.isLt; omega
  have hdN : (d' : ℤ) ≤ N := by have := d'.isLt; omega
  have hacZ : (a : ℤ) < c := by exact_mod_cast hac
  have hcdZ : (c : ℤ) ≤ d' := by exact_mod_cast hcd
  rw [show codimForm N (leftDelta a c d') = codimBil N (leftDelta a c d') (leftDelta a c d') from rfl,
    show leftDelta a c d' = boxℤ (c : ℤ) (d' : ℤ) - boxℤ (a : ℤ) (d' : ℤ) by
        funext α β; simp only [Pi.sub_apply]; rfl]
  simp only [codimBil_sub_left, codimBil_sub_right, codimBil_boxℤ_boxℤ]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  ring

/-- `extendℤ (leftShrink m a c d')` agrees with `extendℤ m + leftDelta` on the box; off the box
`codimForm` does not read the guard. -/
theorem extendℤ_leftShrink_onbox (m : Fin (N + 1) × Fin (N + 1) → ℕ) (a c d' : Fin (N + 1))
    {α β : ℤ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ (N : ℤ)) (hsad : 1 ≤ m (a, d')) (hac : a ≠ c) :
    extendℤ (leftShrink m a c d') α β = (extendℤ m + leftDelta a c d') α β := by
  simp only [Pi.add_apply, extendℤ, leftDelta, boxℤ]
  rw [dif_pos ⟨hα, hαβ, hβ⟩, dif_pos ⟨hα, hαβ, hβ⟩]
  set q : Fin (N + 1) × Fin (N + 1) := (⟨α.toNat, by omega⟩, ⟨β.toNat, by omega⟩) with hq
  have hαβN : (q.1 : ℕ) ≤ q.2 := by rw [hq]; dsimp only [Fin.val_mk]; omega
  have eCD : (q = (c, d')) ↔ (α = (c : ℤ) ∧ β = (d' : ℤ)) := by
    rw [hq, Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]; dsimp only [Fin.val_mk]; omega
  have eAD : (q = (a, d')) ↔ (α = (a : ℤ) ∧ β = (d' : ℤ)) := by
    rw [hq, Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]; dsimp only [Fin.val_mk]; omega
  rw [show leftShrink m a c d' (⟨α.toNat, by omega⟩, ⟨β.toNat, by omega⟩)
      = leftShrink m a c d' q from rfl, leftShrink]
  by_cases h2 : q = (c, d')
  · have h3 : q ≠ (a, d') := fun h ↦ hac (by have := h.symm.trans h2; exact (Prod.mk.injEq .. ▸ this).1)
    rw [if_pos ⟨by rw [h2] at hαβN; exact hαβN, h2⟩, if_neg h3, if_pos (eCD.mp h2),
      if_neg (fun h ↦ h3 (eAD.mpr h))]
    push_cast; ring
  · by_cases h3 : q = (a, d')
    · have hpos : 1 ≤ m q := by rw [h3]; exact hsad
      rw [if_neg (fun h ↦ h2 h.2), if_pos h3, if_neg (fun h ↦ h2 (eCD.mpr h)), if_pos (eAD.mp h3)]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    · rw [if_neg (fun h ↦ h2 h.2), if_neg h3, if_neg (fun h ↦ h2 (eCD.mpr h)),
        if_neg (fun h ↦ h3 (eAD.mpr h))]
      simp only [Nat.add_zero, Nat.sub_zero]; push_cast; ring

/-- **The left-shrink `codimForm`-delta.** `codimForm (extendℤ (leftShrink m a c d')) =
codimForm (extendℤ m) + ∑_Y m̄ Y · leftCoeff a c d' Y` (for `a < c ≤ d'`, source present). -/
theorem codimForm_leftShrink (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a c d' : Fin (N + 1)}
    (hac : (a : ℕ) < c) (hcd : (c : ℕ) ≤ d') (hsad : 1 ≤ m (a, d')) :
    codimForm N (extendℤ (leftShrink m a c d'))
      = codimForm N (extendℤ m)
        + ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * leftCoeff a c d' Y := by
  have hacF : a ≠ c := by rw [Fin.ne_iff_vne]; omega
  rw [codimForm_congr_onbox (fun α β hα hαβ hβ ↦ extendℤ_leftShrink_onbox m a c d' hα hαβ hβ hsad hacF)]
  rw [codimForm_add, codimBil_extendℤ_leftDelta_right, codimBil_leftDelta_extendℤ_left,
    codimForm_leftDelta a c d' hac hcd, add_zero, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun Y _ ↦ by unfold leftCoeff; ring

/-- **Left-shrink sign lemma.** For `c = a + 1 ≤ d'` (omitting the left endpoint `a`), any `Y` with
`leftCoeff a c d' Y > 0` covers `a` and is strictly shorter than `[a,d']`. -/
theorem leftCoeff_pos_imp {a c d' : Fin (N + 1)} (hac : (c : ℕ) = a + 1) (hcd : (c : ℕ) ≤ d')
    {Y : Fin (N + 1) × Fin (N + 1)} (hpos : 0 < leftCoeff a c d' Y) :
    ((Y.1 : ℤ) ≤ (a : ℤ) ∧ (a : ℤ) ≤ (Y.2 : ℤ)) ∧ (Y.2 : ℤ) - (Y.1 : ℤ) < (d' : ℤ) - (a : ℤ) := by
  have hcZ : (c : ℤ) = (a : ℤ) + 1 := by exact_mod_cast hac
  have hcdZ : (c : ℤ) ≤ d' := by exact_mod_cast hcd
  have hY1 : (Y.1 : ℤ) ≤ (N : ℤ) := by have := Y.1.isLt; omega
  have hY2 : (Y.2 : ℤ) ≤ (N : ℤ) := by have := Y.2.isLt; omega
  have haN : (a : ℤ) ≤ (N : ℤ) := by have := a.isLt; omega
  have hdN : (d' : ℤ) ≤ (N : ℤ) := by have := d'.isLt; omega
  have hY1nn : (0 : ℤ) ≤ (Y.1 : ℤ) := by positivity
  have hY2nn : (0 : ℤ) ≤ (Y.2 : ℤ) := by positivity
  have hann : (0 : ℤ) ≤ (a : ℤ) := by positivity
  unfold leftCoeff rrInd llInd at hpos
  split_ifs at hpos <;> omega

/-- **Left-shrink does not increase `codimForm`** when `[a,d']` is a shortest covering interval of its
left endpoint `a` (`c = a + 1`), of positive multiplicity. -/
theorem codimForm_leftShrink_le (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a c d' : Fin (N + 1)}
    (hac : (c : ℕ) = a + 1) (hcd : (c : ℕ) ≤ d') (hsad : 1 ≤ m (a, d'))
    (hshort : ∀ Y : Fin (N + 1) × Fin (N + 1), 1 ≤ m Y →
      (Y.1 : ℤ) ≤ (a : ℤ) → (a : ℤ) ≤ (Y.2 : ℤ) →
      (d' : ℤ) - (a : ℤ) ≤ (Y.2 : ℤ) - (Y.1 : ℤ)) :
    codimForm N (extendℤ (leftShrink m a c d')) ≤ codimForm N (extendℤ m) := by
  rw [codimForm_leftShrink m (by omega) hcd hsad]
  have hsum : ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * leftCoeff a c d' Y ≤ 0 := by
    refine Finset.sum_nonpos fun Y _ ↦ ?_
    rcases lt_or_ge 0 (leftCoeff a c d' Y) with hc | hc
    · obtain ⟨⟨h1, h2⟩, hlen⟩ := leftCoeff_pos_imp hac hcd hc
      have hmY : m Y = 0 := by
        by_contra hne; exact absurd (hshort Y (Nat.one_le_iff_ne_zero.mpr hne) h1 h2) (not_le.mpr hlen)
      rw [hmY]; simp
    · exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hc
  linarith

/-- Filtered-coverage change of `leftShrink` (as `ℤ`): coverage of `m` plus the guarded `[c,d']`
indicator minus the `[a,d']` indicator. -/
theorem leftShrink_cover (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a c d' : Fin (N + 1)}
    (hac : (a : ℕ) < c) (hcd : (c : ℕ) ≤ d') (hsad : 1 ≤ m (a, d')) (v : Fin (N + 1)) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
        leftShrink m a c d' p : ℤ)
      = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2), m p : ℤ)
        + (if c ≤ d' ∧ c ≤ v ∧ v ≤ d' then 1 else 0) - (if a ≤ v ∧ v ≤ d' then 1 else 0) := by
  set S := Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2) with hS
  have hacF : a ≠ c := by rw [Fin.ne_iff_vne]; omega
  have hterm : ∀ p : Fin (N + 1) × Fin (N + 1),
      ((leftShrink m a c d' p : ℕ) : ℤ)
        = (m p : ℤ) + (if c ≤ d' ∧ p = (c, d') then 1 else 0) - (if p = (a, d') then 1 else 0) := by
    intro p
    by_cases h2 : c ≤ d' ∧ p = (c, d')
    · have h3 : p ≠ (a, d') := by rw [h2.2]; intro h; exact hacF (congrArg Prod.fst h).symm
      simp only [leftShrink, if_pos h2, if_neg h3, Nat.add_zero, Nat.sub_zero]; push_cast; ring
    · by_cases h3 : p = (a, d')
      · have hpos : 1 ≤ m p := by rw [h3]; exact hsad
        simp only [leftShrink, if_neg h2, if_pos h3, Nat.add_zero]
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      · simp only [leftShrink, if_neg h2, if_neg h3, Nat.add_zero, Nat.sub_zero]; push_cast; ring
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ S) ↦ hterm p), Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  have hcollapse : ∀ (P : Prop) [Decidable P] (key : Fin (N + 1) × Fin (N + 1)),
      (∑ p ∈ S, if P ∧ p = key then (1 : ℤ) else 0) = if P ∧ key ∈ S then 1 else 0 := by
    intro P _ key
    by_cases hP : P
    · simp only [hP, true_and]; rw [Finset.sum_ite_eq' S key]
    · simp only [hP, false_and, if_false, Finset.sum_const_zero]
  rw [hcollapse (c ≤ d') (c, d'), Finset.sum_ite_eq' S (a, d')]
  have hmemS : ∀ x y : Fin (N + 1), ((x, y) ∈ S) ↔ (x ≤ v ∧ v ≤ y) := by
    intro x y; rw [hS]; simp [Finset.mem_filter]
  simp only [hmemS]

/-- **Left-shrink lands in the corner-`0` Kostant partitions of the vector decremented at `a`.** For
`[a,d']` covering its left endpoint, present, and `≠ [0,N]` (corner stays `0`). -/
theorem leftShrink_mem {e' : Fin (N + 1) → ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    {a c d' : Fin (N + 1)} (hm : m ∈ kostantPartitions e' 0)
    (hac : (c : ℕ) = a + 1) (hcd : (c : ℕ) ≤ d') (had : a ≤ d') (hsad : 1 ≤ m (a, d'))
    (hcorner : (a, d') ≠ ((0 : Fin (N + 1)), Fin.last N)) :
    leftShrink m a c d' ∈ kostantPartitions (Function.update e' a (e' a - 1)) 0 := by
  obtain ⟨hbnd, hsupp, hkost, hc0⟩ := mem_kostantPartitions.mp hm
  have hac0 : (a : ℕ) < c := by omega
  have hsupp' : ∀ p, ¬ p.1 ≤ p.2 → leftShrink m a c d' p = 0 := by
    intro p hp
    have h2 : ¬ (c ≤ d' ∧ p = (c, d')) := fun h ↦ hp (by rw [h.2]; exact (Fin.le_def.mpr hcd))
    have h3 : p ≠ (a, d') := fun h ↦ hp (by rw [h]; exact had)
    simp only [leftShrink, if_neg h2, if_neg h3, Nat.add_zero, Nat.sub_zero]; exact hsupp p hp
  have hekpos : 1 ≤ e' a := by
    rw [hkost a]
    refine le_trans hsad (Finset.single_le_sum (fun q _ ↦ Nat.zero_le _) ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨le_rfl, had⟩
  have hkost' : ∀ v, kostantAt (Function.update e' a (e' a - 1)) (leftShrink m a c d') v := by
    intro v
    rw [kostantAt]
    have hcov := leftShrink_cover m hac0 hcd hsad v
    have hbase : (e' v : ℤ)
        = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
            m p : ℤ) := by exact_mod_cast hkost v
    have hZ : ((Function.update e' a (e' a - 1) v : ℕ) : ℤ)
        = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
            leftShrink m a c d' p : ℤ) := by
      rw [hcov, ← hbase]
      have hupd : ((Function.update e' a (e' a - 1) v : ℕ) : ℤ)
          = (e' v : ℤ) - (if v = a then 1 else 0) := by
        by_cases hva : v = a
        · subst hva; rw [Function.update_self, if_pos rfl, Nat.cast_sub hekpos]; push_cast; ring
        · rw [Function.update_of_ne hva, if_neg hva]; ring
      rw [hupd]
      have hvaN : (v = a) ↔ ((v : ℕ) = a) := by rw [Fin.ext_iff]
      simp only [Fin.le_def, hvaN]
      split_ifs <;> omega
    exact_mod_cast hZ
  refine mem_kostantPartitions.mpr ⟨bound_of_kostant hsupp' hkost', hsupp', hkost', ?_⟩
  · have hdN : (d' : ℕ) ≤ N := by have := d'.isLt; omega
    have h2 : ¬ (c ≤ d' ∧ ((0 : Fin (N + 1)), Fin.last N) = (c, d')) := by
      rintro ⟨-, hh⟩; rw [Prod.mk.injEq] at hh; have := hh.1
      rw [Fin.ext_iff, Fin.val_zero] at this; omega
    have h3 : ((0 : Fin (N + 1)), Fin.last N) ≠ (a, d') := fun h ↦ hcorner h.symm
    show leftShrink m a c d' ((0 : Fin (N + 1)), Fin.last N) = 0
    simp only [leftShrink, if_neg h2, if_neg h3, Nat.add_zero, Nat.sub_zero]
    exact hc0

/-! ### The right-shrink (omitting the right endpoint `d'`) -/

/-- The right-shrink move: replace one copy of `[a,d']` by `[a,b]` (kept only when `a ≤ b`), omitting
the right endpoint `d'` (`b = d'−1`). -/
def rightShrink (m : Fin (N + 1) × Fin (N + 1) → ℕ) (a b d' : Fin (N + 1)) :
    Fin (N + 1) × Fin (N + 1) → ℕ :=
  fun p ↦ m p + (if a ≤ b ∧ p = (a, b) then 1 else 0) - (if p = (a, d') then 1 else 0)

/-- The right-shrink ℤ-delta: `boxℤ a b − boxℤ a d'`. -/
def rightDelta (a b d' : Fin (N + 1)) : ℤ → ℤ → ℤ :=
  fun α β ↦ boxℤ (a : ℤ) (b : ℤ) α β - boxℤ (a : ℤ) (d' : ℤ) α β

/-- Per-interval coefficient of the right-shrink delta. -/
def rightCoeff (a b d' : Fin (N + 1)) (Y : Fin (N + 1) × Fin (N + 1)) : ℤ :=
  ((if rrInd (a : ℤ) (b : ℤ) Y then 1 else 0) - (if rrInd (a : ℤ) (d' : ℤ) Y then 1 else 0))
  + ((if llInd (a : ℤ) (b : ℤ) Y then 1 else 0) - (if llInd (a : ℤ) (d' : ℤ) Y then 1 else 0))

/-- `codimBil (extendℤ m) (rightDelta …)` as a per-interval `univ`-sum (right-rectangle indicators). -/
theorem codimBil_extendℤ_rightDelta_right (m : Fin (N + 1) × Fin (N + 1) → ℕ)
    (a b d' : Fin (N + 1)) :
    codimBil N (extendℤ m) (rightDelta a b d')
      = ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ)
          * ((if rrInd (a : ℤ) (b : ℤ) Y then 1 else 0)
              - (if rrInd (a : ℤ) (d' : ℤ) Y then 1 else 0)) := by
  have hbox : ∀ p q : ℤ, codimBil N (extendℤ m) (boxℤ p q)
      = ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * (if rrInd p q Y then 1 else 0) := by
    intro p q
    rw [codimBil_extendℤ_boxℤ_right, Finset.sum_filter]
    exact Finset.sum_congr rfl fun Y _ ↦ by split_ifs with h <;> simp
  rw [show rightDelta a b d' = boxℤ (a : ℤ) (b : ℤ) - boxℤ (a : ℤ) (d' : ℤ) by
        funext α β; simp only [Pi.sub_apply]; rfl,
    codimBil_sub_right, hbox, hbox, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun Y _ ↦ by ring

/-- `codimBil (rightDelta …) (extendℤ m)` as a per-interval `univ`-sum (left-rectangle indicators). -/
theorem codimBil_rightDelta_extendℤ_left (m : Fin (N + 1) × Fin (N + 1) → ℕ) (a b d' : Fin (N + 1)) :
    codimBil N (rightDelta a b d') (extendℤ m)
      = ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ)
          * ((if llInd (a : ℤ) (b : ℤ) Y then 1 else 0)
              - (if llInd (a : ℤ) (d' : ℤ) Y then 1 else 0)) := by
  have hbox : ∀ p q : ℤ, codimBil N (boxℤ p q) (extendℤ m)
      = ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * (if llInd p q Y then 1 else 0) := by
    intro p q
    rw [codimBil_boxℤ_extendℤ_left, Finset.sum_filter]
    exact Finset.sum_congr rfl fun Y _ ↦ by split_ifs with h <;> simp
  rw [show rightDelta a b d' = boxℤ (a : ℤ) (b : ℤ) - boxℤ (a : ℤ) (d' : ℤ) by
        funext α β; simp only [Pi.sub_apply]; rfl,
    codimBil_sub_left, hbox, hbox, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun Y _ ↦ by ring

/-- The right-shrink self-term `codimForm (rightDelta …) = 0` (for `a ≤ b < d'`). -/
theorem codimForm_rightDelta (a b d' : Fin (N + 1)) (hab : (a : ℕ) ≤ b) (hbd : (b : ℕ) < d') :
    codimForm N (rightDelta a b d') = 0 := by
  have hbN : (b : ℤ) ≤ N := by have := b.isLt; omega
  have hdN : (d' : ℤ) ≤ N := by have := d'.isLt; omega
  have habZ : (a : ℤ) ≤ b := by exact_mod_cast hab
  have hbdZ : (b : ℤ) < d' := by exact_mod_cast hbd
  rw [show codimForm N (rightDelta a b d') = codimBil N (rightDelta a b d') (rightDelta a b d') from rfl,
    show rightDelta a b d' = boxℤ (a : ℤ) (b : ℤ) - boxℤ (a : ℤ) (d' : ℤ) by
        funext α β; simp only [Pi.sub_apply]; rfl]
  simp only [codimBil_sub_left, codimBil_sub_right, codimBil_boxℤ_boxℤ]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  ring

/-- `extendℤ (rightShrink …)` agrees with `extendℤ m + rightDelta` on the box. -/
theorem extendℤ_rightShrink_onbox (m : Fin (N + 1) × Fin (N + 1) → ℕ) (a b d' : Fin (N + 1))
    {α β : ℤ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ (N : ℤ)) (hsad : 1 ≤ m (a, d')) (hbd : b ≠ d') :
    extendℤ (rightShrink m a b d') α β = (extendℤ m + rightDelta a b d') α β := by
  simp only [Pi.add_apply, extendℤ, rightDelta, boxℤ]
  rw [dif_pos ⟨hα, hαβ, hβ⟩, dif_pos ⟨hα, hαβ, hβ⟩]
  set q : Fin (N + 1) × Fin (N + 1) := (⟨α.toNat, by omega⟩, ⟨β.toNat, by omega⟩) with hq
  have hαβN : (q.1 : ℕ) ≤ q.2 := by rw [hq]; dsimp only [Fin.val_mk]; omega
  have eAB : (q = (a, b)) ↔ (α = (a : ℤ) ∧ β = (b : ℤ)) := by
    rw [hq, Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]; dsimp only [Fin.val_mk]; omega
  have eAD : (q = (a, d')) ↔ (α = (a : ℤ) ∧ β = (d' : ℤ)) := by
    rw [hq, Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]; dsimp only [Fin.val_mk]; omega
  rw [show rightShrink m a b d' (⟨α.toNat, by omega⟩, ⟨β.toNat, by omega⟩)
      = rightShrink m a b d' q from rfl, rightShrink]
  by_cases h1 : q = (a, b)
  · have h3 : q ≠ (a, d') := fun h ↦ hbd (by have := h1.symm.trans h; exact (Prod.mk.injEq .. ▸ this).2)
    rw [if_pos ⟨by rw [h1] at hαβN; exact hαβN, h1⟩, if_neg h3, if_pos (eAB.mp h1),
      if_neg (fun h ↦ h3 (eAD.mpr h))]
    push_cast; ring
  · by_cases h3 : q = (a, d')
    · have hpos : 1 ≤ m q := by rw [h3]; exact hsad
      rw [if_neg (fun h ↦ h1 h.2), if_pos h3, if_neg (fun h ↦ h1 (eAB.mpr h)), if_pos (eAD.mp h3)]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    · rw [if_neg (fun h ↦ h1 h.2), if_neg h3, if_neg (fun h ↦ h1 (eAB.mpr h)),
        if_neg (fun h ↦ h3 (eAD.mpr h))]
      simp only [Nat.add_zero, Nat.sub_zero]; push_cast; ring

/-- **The right-shrink `codimForm`-delta.** -/
theorem codimForm_rightShrink (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a b d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbd : (b : ℕ) < d') (hsad : 1 ≤ m (a, d')) :
    codimForm N (extendℤ (rightShrink m a b d'))
      = codimForm N (extendℤ m)
        + ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * rightCoeff a b d' Y := by
  have hbdF : b ≠ d' := by rw [Fin.ne_iff_vne]; omega
  rw [codimForm_congr_onbox (fun α β hα hαβ hβ ↦ extendℤ_rightShrink_onbox m a b d' hα hαβ hβ hsad hbdF)]
  rw [codimForm_add, codimBil_extendℤ_rightDelta_right, codimBil_rightDelta_extendℤ_left,
    codimForm_rightDelta a b d' hab hbd, add_zero, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun Y _ ↦ by unfold rightCoeff; ring

/-- **Right-shrink sign lemma.** For `b = d' − 1` (`b + 1 = d'`, omitting the right endpoint `d'`),
any `Y` with `rightCoeff a b d' Y > 0` covers `d'` and is strictly shorter than `[a,d']`. -/
theorem rightCoeff_pos_imp {a b d' : Fin (N + 1)} (hab : (a : ℕ) ≤ b) (hbd : (b : ℕ) + 1 = d')
    {Y : Fin (N + 1) × Fin (N + 1)} (hpos : 0 < rightCoeff a b d' Y) :
    ((Y.1 : ℤ) ≤ (d' : ℤ) ∧ (d' : ℤ) ≤ (Y.2 : ℤ)) ∧ (Y.2 : ℤ) - (Y.1 : ℤ) < (d' : ℤ) - (a : ℤ) := by
  have hbdZ : (b : ℤ) + 1 = d' := by exact_mod_cast hbd
  have habZ : (a : ℤ) ≤ b := by exact_mod_cast hab
  have hY1 : (Y.1 : ℤ) ≤ (N : ℤ) := by have := Y.1.isLt; omega
  have hY2 : (Y.2 : ℤ) ≤ (N : ℤ) := by have := Y.2.isLt; omega
  have haN : (a : ℤ) ≤ (N : ℤ) := by have := a.isLt; omega
  have hbN : (b : ℤ) ≤ (N : ℤ) := by have := b.isLt; omega
  have hY1nn : (0 : ℤ) ≤ (Y.1 : ℤ) := by positivity
  have hY2nn : (0 : ℤ) ≤ (Y.2 : ℤ) := by positivity
  have hann : (0 : ℤ) ≤ (a : ℤ) := by positivity
  unfold rightCoeff rrInd llInd at hpos
  split_ifs at hpos <;> omega

/-- **Right-shrink does not increase `codimForm`** when `[a,d']` is a shortest covering interval of
its right endpoint `d'` (`b = d' − 1`), of positive multiplicity. -/
theorem codimForm_rightShrink_le (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a b d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbd : (b : ℕ) + 1 = d') (hsad : 1 ≤ m (a, d'))
    (hshort : ∀ Y : Fin (N + 1) × Fin (N + 1), 1 ≤ m Y →
      (Y.1 : ℤ) ≤ (d' : ℤ) → (d' : ℤ) ≤ (Y.2 : ℤ) →
      (d' : ℤ) - (a : ℤ) ≤ (Y.2 : ℤ) - (Y.1 : ℤ)) :
    codimForm N (extendℤ (rightShrink m a b d')) ≤ codimForm N (extendℤ m) := by
  rw [codimForm_rightShrink m hab (by omega) hsad]
  have hsum : ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * rightCoeff a b d' Y ≤ 0 := by
    refine Finset.sum_nonpos fun Y _ ↦ ?_
    rcases lt_or_ge 0 (rightCoeff a b d' Y) with hc | hc
    · obtain ⟨⟨h1, h2⟩, hlen⟩ := rightCoeff_pos_imp hab hbd hc
      have hmY : m Y = 0 := by
        by_contra hne; exact absurd (hshort Y (Nat.one_le_iff_ne_zero.mpr hne) h1 h2) (not_le.mpr hlen)
      rw [hmY]; simp
    · exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hc
  linarith

/-- Filtered-coverage change of `rightShrink` (as `ℤ`). -/
theorem rightShrink_cover (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a b d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbd : (b : ℕ) < d') (hsad : 1 ≤ m (a, d')) (v : Fin (N + 1)) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
        rightShrink m a b d' p : ℤ)
      = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2), m p : ℤ)
        + (if a ≤ b ∧ a ≤ v ∧ v ≤ b then 1 else 0) - (if a ≤ v ∧ v ≤ d' then 1 else 0) := by
  set S := Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2) with hS
  have hbdF : b ≠ d' := by rw [Fin.ne_iff_vne]; omega
  have hterm : ∀ p : Fin (N + 1) × Fin (N + 1),
      ((rightShrink m a b d' p : ℕ) : ℤ)
        = (m p : ℤ) + (if a ≤ b ∧ p = (a, b) then 1 else 0) - (if p = (a, d') then 1 else 0) := by
    intro p
    by_cases h1 : a ≤ b ∧ p = (a, b)
    · have h3 : p ≠ (a, d') := by rw [h1.2]; intro h; exact hbdF (congrArg Prod.snd h)
      simp only [rightShrink, if_pos h1, if_neg h3, Nat.add_zero, Nat.sub_zero]; push_cast; ring
    · by_cases h3 : p = (a, d')
      · have hpos : 1 ≤ m p := by rw [h3]; exact hsad
        simp only [rightShrink, if_neg h1, if_pos h3, Nat.add_zero]
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      · simp only [rightShrink, if_neg h1, if_neg h3, Nat.add_zero, Nat.sub_zero]; push_cast; ring
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ S) ↦ hterm p), Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  have hcollapse : ∀ (P : Prop) [Decidable P] (key : Fin (N + 1) × Fin (N + 1)),
      (∑ p ∈ S, if P ∧ p = key then (1 : ℤ) else 0) = if P ∧ key ∈ S then 1 else 0 := by
    intro P _ key
    by_cases hP : P
    · simp only [hP, true_and]; rw [Finset.sum_ite_eq' S key]
    · simp only [hP, false_and, if_false, Finset.sum_const_zero]
  rw [hcollapse (a ≤ b) (a, b), Finset.sum_ite_eq' S (a, d')]
  have hmemS : ∀ x y : Fin (N + 1), ((x, y) ∈ S) ↔ (x ≤ v ∧ v ≤ y) := by
    intro x y; rw [hS]; simp [Finset.mem_filter]
  simp only [hmemS]

/-- **Right-shrink lands in the corner-`0` Kostant partitions of the vector decremented at `d'`.** -/
theorem rightShrink_mem {e' : Fin (N + 1) → ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    {a b d' : Fin (N + 1)} (hm : m ∈ kostantPartitions e' 0)
    (hab : a ≤ b) (hbd : (b : ℕ) + 1 = d') (had : a ≤ d') (hsad : 1 ≤ m (a, d'))
    (hcorner : (a, d') ≠ ((0 : Fin (N + 1)), Fin.last N)) :
    rightShrink m a b d' ∈ kostantPartitions (Function.update e' d' (e' d' - 1)) 0 := by
  obtain ⟨hbnd, hsupp, hkost, hc0⟩ := mem_kostantPartitions.mp hm
  have habN : (a : ℕ) ≤ b := Fin.le_def.mp hab
  have hsupp' : ∀ p, ¬ p.1 ≤ p.2 → rightShrink m a b d' p = 0 := by
    intro p hp
    have h1 : ¬ (a ≤ b ∧ p = (a, b)) := fun h ↦ hp (by rw [h.2]; exact h.1)
    have h3 : p ≠ (a, d') := fun h ↦ hp (by rw [h]; exact had)
    simp only [rightShrink, if_neg h1, if_neg h3, Nat.add_zero, Nat.sub_zero]; exact hsupp p hp
  have hekpos : 1 ≤ e' d' := by
    rw [hkost d']
    refine le_trans hsad (Finset.single_le_sum (fun q _ ↦ Nat.zero_le _) ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨had, le_rfl⟩
  have hkost' : ∀ v, kostantAt (Function.update e' d' (e' d' - 1)) (rightShrink m a b d') v := by
    intro v
    rw [kostantAt]
    have hcov := rightShrink_cover m habN (by omega) hsad v
    have hbase : (e' v : ℤ)
        = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
            m p : ℤ) := by exact_mod_cast hkost v
    have hZ : ((Function.update e' d' (e' d' - 1) v : ℕ) : ℤ)
        = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
            rightShrink m a b d' p : ℤ) := by
      rw [hcov, ← hbase]
      have hupd : ((Function.update e' d' (e' d' - 1) v : ℕ) : ℤ)
          = (e' v : ℤ) - (if v = d' then 1 else 0) := by
        by_cases hvd : v = d'
        · subst hvd; rw [Function.update_self, if_pos rfl, Nat.cast_sub hekpos]; push_cast; ring
        · rw [Function.update_of_ne hvd, if_neg hvd]; ring
      rw [hupd]
      have hvdN : (v = d') ↔ ((v : ℕ) = d') := by rw [Fin.ext_iff]
      simp only [Fin.le_def, hvdN]
      split_ifs <;> omega
    exact_mod_cast hZ
  refine mem_kostantPartitions.mpr ⟨bound_of_kostant hsupp' hkost', hsupp', hkost', ?_⟩
  · have hdN : (d' : ℕ) ≤ N := by have := d'.isLt; omega
    have h1 : ¬ (a ≤ b ∧ ((0 : Fin (N + 1)), Fin.last N) = (a, b)) := by
      rintro ⟨-, hh⟩; rw [Prod.mk.injEq] at hh; have := hh.2
      rw [Fin.ext_iff, Fin.val_last] at this; omega
    have h3 : ((0 : Fin (N + 1)), Fin.last N) ≠ (a, d') := fun h ↦ hcorner h.symm
    show rightShrink m a b d' ((0 : Fin (N + 1)), Fin.last N) = 0
    simp only [rightShrink, if_neg h1, if_neg h3, Nat.add_zero, Nat.sub_zero]
    exact hc0

/-! ### Singleton removal (omitting both endpoints of `[a,a]`) -/

/-- The singleton-removal move: drop one copy of `[a,a]` (omitting vertex `a`). -/
def removeMove (m : Fin (N + 1) × Fin (N + 1) → ℕ) (a : Fin (N + 1)) :
    Fin (N + 1) × Fin (N + 1) → ℕ :=
  fun p ↦ m p - (if p = (a, a) then 1 else 0)

/-- The singleton-removal ℤ-delta: `−boxℤ a a` (as a raw lambda, mirroring `splitDelta`). -/
def removeDelta (a : Fin (N + 1)) : ℤ → ℤ → ℤ := fun α β ↦ - boxℤ (a : ℤ) (a : ℤ) α β

/-- Per-interval coefficient of the singleton-removal delta. -/
def removeCoeff (a : Fin (N + 1)) (Y : Fin (N + 1) × Fin (N + 1)) : ℤ :=
  -((if rrInd (a : ℤ) (a : ℤ) Y then 1 else 0) + (if llInd (a : ℤ) (a : ℤ) Y then 1 else 0))

/-- `extendℤ (removeMove m a) = extendℤ m + removeDelta a` (source `[a,a]` present). -/
theorem extendℤ_removeMove {m : Fin (N + 1) × Fin (N + 1) → ℕ} {a : Fin (N + 1)}
    (hsa : 1 ≤ m (a, a)) :
    extendℤ (removeMove m a) = extendℤ m + removeDelta a := by
  funext α β
  simp only [Pi.add_apply, extendℤ, removeDelta, boxℤ]
  by_cases hbox : (0 : ℤ) ≤ α ∧ α ≤ β ∧ β ≤ (N : ℤ)
  · rw [dif_pos hbox, dif_pos hbox]
    obtain ⟨hα0, hαβ, hβN⟩ := hbox
    set q : Fin (N + 1) × Fin (N + 1) := (⟨α.toNat, by omega⟩, ⟨β.toNat, by omega⟩) with hq
    have eAA : (q = (a, a)) ↔ (α = (a : ℤ) ∧ β = (a : ℤ)) := by
      rw [hq, Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]; dsimp only [Fin.val_mk]; omega
    rw [show removeMove m a (⟨α.toNat, by omega⟩, ⟨β.toNat, by omega⟩) = removeMove m a q from rfl,
      removeMove]
    by_cases h1 : q = (a, a)
    · have hpos : 1 ≤ m q := by rw [h1]; exact hsa
      rw [if_pos h1, if_pos (eAA.mp h1), Nat.cast_sub (by omega)]; push_cast; ring
    · rw [if_neg h1, if_neg (fun h ↦ h1 (eAA.mpr h)), Nat.sub_zero]; push_cast; ring
  · simp only [dif_neg hbox]
    have haN : (a : ℤ) ≤ N := by have := a.isLt; omega
    rw [if_neg (by rintro ⟨h1, h2⟩; exact hbox ⟨by omega, by omega, by omega⟩)]; ring

/-- **The singleton-removal `codimForm`-delta.** -/
theorem codimForm_removeMove (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a : Fin (N + 1)}
    (hsa : 1 ≤ m (a, a)) :
    codimForm N (extendℤ (removeMove m a))
      = codimForm N (extendℤ m) + ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * removeCoeff a Y := by
  have hbr : codimBil N (extendℤ m) (removeDelta a)
      = ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ)
          * (-(if rrInd (a : ℤ) (a : ℤ) Y then 1 else 0)) := by
    rw [show removeDelta a = (0 : ℤ → ℤ → ℤ) - boxℤ (a : ℤ) (a : ℤ) by
          funext α β; simp only [removeDelta, Pi.sub_apply, Pi.zero_apply]; ring,
      codimBil_sub_right, codimBil_extendℤ_boxℤ_right, Finset.sum_filter]
    have hz : codimBil N (extendℤ m) (0 : ℤ → ℤ → ℤ) = 0 := by unfold codimBil; simp
    rw [hz, zero_sub, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun Y _ ↦ by split_ifs with h <;> simp
  have hbl : codimBil N (removeDelta a) (extendℤ m)
      = ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ)
          * (-(if llInd (a : ℤ) (a : ℤ) Y then 1 else 0)) := by
    rw [show removeDelta a = (0 : ℤ → ℤ → ℤ) - boxℤ (a : ℤ) (a : ℤ) by
          funext α β; simp only [removeDelta, Pi.sub_apply, Pi.zero_apply]; ring,
      codimBil_sub_left, codimBil_boxℤ_extendℤ_left, Finset.sum_filter]
    have hz : codimBil N (0 : ℤ → ℤ → ℤ) (extendℤ m) = 0 := by unfold codimBil; simp
    rw [hz, zero_sub, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun Y _ ↦ by split_ifs with h <;> simp
  have hself : codimForm N (removeDelta a) = 0 := by
    rw [show codimForm N (removeDelta a) = codimBil N (removeDelta a) (removeDelta a) from rfl,
      show removeDelta a = (0 : ℤ → ℤ → ℤ) - boxℤ (a : ℤ) (a : ℤ) by
          funext α β; simp only [removeDelta, Pi.sub_apply, Pi.zero_apply]; ring]
    have hz1 : codimBil N (0 : ℤ → ℤ → ℤ) (0 : ℤ → ℤ → ℤ) = 0 := by unfold codimBil; simp
    have hz2 : codimBil N (0 : ℤ → ℤ → ℤ) (boxℤ (a : ℤ) (a : ℤ)) = 0 := by unfold codimBil; simp
    have hz3 : codimBil N (boxℤ (a : ℤ) (a : ℤ)) (0 : ℤ → ℤ → ℤ) = 0 := by unfold codimBil; simp
    have haN : (a : ℤ) ≤ N := by have := a.isLt; omega
    rw [codimBil_sub_left, codimBil_sub_right, codimBil_sub_right, hz1, hz2, hz3,
      codimBil_boxℤ_boxℤ, if_neg (by omega)]; ring
  rw [extendℤ_removeMove hsa, codimForm_add, hbr, hbl, hself, add_zero, add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun Y _ ↦ by unfold removeCoeff; ring

/-- Every coefficient of the singleton-removal delta is `≤ 0` (the omitted `[a,a]` has length `0`, so
no covering interval is strictly shorter). -/
theorem removeCoeff_nonpos (a : Fin (N + 1)) (Y : Fin (N + 1) × Fin (N + 1)) :
    removeCoeff a Y ≤ 0 := by
  unfold removeCoeff; split_ifs <;> omega

/-- **Singleton removal does not increase `codimForm`.** -/
theorem codimForm_removeMove_le (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a : Fin (N + 1)}
    (hsa : 1 ≤ m (a, a)) :
    codimForm N (extendℤ (removeMove m a)) ≤ codimForm N (extendℤ m) := by
  rw [codimForm_removeMove m hsa]
  have hsum : ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * removeCoeff a Y ≤ 0 :=
    Finset.sum_nonpos fun Y _ ↦ mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _)
      (removeCoeff_nonpos a Y)
  linarith

/-- Filtered-coverage change of `removeMove`. -/
theorem removeMove_cover (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a : Fin (N + 1)}
    (hsa : 1 ≤ m (a, a)) (v : Fin (N + 1)) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
        removeMove m a p : ℤ)
      = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2), m p : ℤ)
        - (if a ≤ v ∧ v ≤ a then 1 else 0) := by
  set S := Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2) with hS
  have hterm : ∀ p : Fin (N + 1) × Fin (N + 1),
      ((removeMove m a p : ℕ) : ℤ) = (m p : ℤ) - (if p = (a, a) then 1 else 0) := by
    intro p
    by_cases h1 : p = (a, a)
    · have hpos : 1 ≤ m p := by rw [h1]; exact hsa
      simp only [removeMove, if_pos h1]; rw [Nat.cast_sub (by omega)]; push_cast; ring
    · simp only [removeMove, if_neg h1, Nat.sub_zero]; push_cast; ring
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ S) ↦ hterm p), Finset.sum_sub_distrib,
    Finset.sum_ite_eq' S (a, a)]
  have hmemS : ((a, a) ∈ S) ↔ (a ≤ v ∧ v ≤ a) := by rw [hS]; simp [Finset.mem_filter]
  simp only [hmemS]

/-- **Singleton removal lands in the corner-`0` Kostant partitions of the vector decremented at `a`.**
-/
theorem removeMove_mem {e' : Fin (N + 1) → ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ} {a : Fin (N + 1)}
    (hm : m ∈ kostantPartitions e' 0) (hsa : 1 ≤ m (a, a)) :
    removeMove m a ∈ kostantPartitions (Function.update e' a (e' a - 1)) 0 := by
  obtain ⟨hbnd, hsupp, hkost, hc0⟩ := mem_kostantPartitions.mp hm
  have hsupp' : ∀ p, ¬ p.1 ≤ p.2 → removeMove m a p = 0 := by
    intro p hp
    have h1 : p ≠ (a, a) := fun h ↦ hp (by rw [h])
    simp only [removeMove, if_neg h1, Nat.sub_zero]; exact hsupp p hp
  have hekpos : 1 ≤ e' a := by
    rw [hkost a]
    refine le_trans hsa (Finset.single_le_sum (fun q _ ↦ Nat.zero_le _) ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨le_rfl, le_rfl⟩
  have hkost' : ∀ v, kostantAt (Function.update e' a (e' a - 1)) (removeMove m a) v := by
    intro v
    rw [kostantAt]
    have hcov := removeMove_cover m hsa v
    have hbase : (e' v : ℤ)
        = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
            m p : ℤ) := by exact_mod_cast hkost v
    have hZ : ((Function.update e' a (e' a - 1) v : ℕ) : ℤ)
        = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ v ∧ v ≤ p.2),
            removeMove m a p : ℤ) := by
      rw [hcov, ← hbase]
      have hupd : ((Function.update e' a (e' a - 1) v : ℕ) : ℤ)
          = (e' v : ℤ) - (if v = a then 1 else 0) := by
        by_cases hva : v = a
        · subst hva; rw [Function.update_self, if_pos rfl, Nat.cast_sub hekpos]; push_cast; ring
        · rw [Function.update_of_ne hva, if_neg hva]; ring
      rw [hupd]
      have hva : (v = a) ↔ (a ≤ v ∧ v ≤ a) :=
        ⟨fun h ↦ by subst h; exact ⟨le_rfl, le_rfl⟩, fun ⟨h1, h2⟩ ↦ le_antisymm h2 h1⟩
      simp only [hva]
    exact_mod_cast hZ
  refine mem_kostantPartitions.mpr ⟨bound_of_kostant hsupp' hkost', hsupp', hkost', ?_⟩
  · have h1 : ((0 : Fin (N + 1)), Fin.last N) ≠ (a, a) := by
      intro hh; rw [← hh, hc0] at hsa; exact absurd hsa (by norm_num)
    show removeMove m a ((0 : Fin (N + 1)), Fin.last N) = 0
    simp only [removeMove, if_neg h1, Nat.sub_zero]
    exact hc0

end DLNFibre.Core
