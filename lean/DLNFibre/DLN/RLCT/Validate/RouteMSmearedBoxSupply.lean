import DLNFibre.DLN.RLCT.Validate.RouteMSmearedUniformLam
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedWaist

/-!
# `RouteMSmearedBoxSupply` — the general-`L` smeared box supplier (item 3, the instantiation)

Ties R1 (the box determinants) + R2 (the Field-A `hSpre_gen`) + the uniform-`u` `Λ₀`/Gram bounds
(`RouteMSmearedUniformLam`) + the width-`r` waist (`RouteMSmearedWaist`) into the per-ε
`SmearedChartData` the general-`L` chart consumes, then into the unconditional `hSmeared` ∀L.

The load-bearing choice is a single `η*` (a function of `δ`) that simultaneously satisfies:
* `boxGen`'s carrier constraint (`η* ≤ δ`, `0 < η*`, `η* ≤ 1`);
* the Gram / waist det small-`η` margin `r·(η*·Acc_G) < (δ/2)^{L−1}` (`Acc_G` `η`-free);
* the `Λ₀`-dominance margin `(r−1)·(η*·Acc_Λ) < (δ/2)^{L−1−q} − η*·Acc_Λ` (`γ* > 0`);
* the Field-A margin `s·((1/γ*)·(η*·Acc_Λ))·η* ≤ δ`.
All `Acc`s are `η`-free (the suffix recursion reads `M, δ` only), so each is "pick `η*` small".

* `condBox_boxGen_frontLayers` — points in the `boxGen` condBox have front `CarrierLayer`s.
* `insertNth_hN_mem_condBox` — a peeled point `hN ▸ insertNth p z y` is in the `boxGen` condBox.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

open DLNFibre.Core.Matrix

variable {L : ℕ} {M : Fin (L + 1) → ℕ} {r s : ℕ}

/-! ## Front `CarrierLayer`s from a `boxGen` condBox point -/

/-- **The front-slot coord of a free layer `t.val < L−1` is not the pivot** (`t ≠ deepLayer`, so the
front slot is not a top slot, but the pivot IS a top slot). -/
theorem coordOfG_frontSlotG_ne_pivot (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (t : Fin L) (ht : (t : ℕ) < L - 1) (i : Fin (M t.castSucc)) (j : Fin (M t.succ)) :
    coordOfG M (frontSlotG M t i j) ≠ pivotCoordG M hL hrs hr hc := by
  have htd : t ≠ deepLayer hL := by
    intro h; rw [h] at ht; simp only [deepLayer] at ht; omega
  intro heq
  have hmem : coordOfG M (frontSlotG M t i j) ∈ topCoordsG M hL hrs := by
    rw [heq]; exact pivotCoordG_mem M hL hrs hr hc
  exact coordOfG_frontSlotG_not_mem M hL hrs t htd i j hmem

/-- **A `boxGen` condBox point has front `CarrierLayer`s.** For `u` with `∀ k ≠ pivotCoordG, u k ∈ boxGen
r δ η k`, every free front layer `t.val < L−1` of `frontTupleG M u` is a `CarrierLayer r δ η`: at that
layer each front slot's coord `≠ pivotCoordG` (`coordOfG_frontSlotG_ne_pivot`), so it lies in
`boxGen = slotBoxGen`, whose diagonal / off-diagonal branches give the carrier structure. -/
theorem condBox_boxGen_frontLayers (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    {δ η : ℝ} {u : Fin (routeMAmbient M) → ℝ}
    (hu : ∀ k, k ≠ pivotCoordG M hL hrs hr hc → u k ∈ boxGen M hL r δ η k)
    (t : Fin L) (ht : (t : ℕ) < L - 1) :
    CarrierLayer (frontTupleG M u t) r δ η := by
  -- the box membership at this layer's front slots
  have hslot : ∀ i : Fin (M t.castSucc), ∀ j : Fin (M t.succ),
      u (coordOfG M (frontSlotG M t i j)) ∈ slotBoxGen M hL r δ η (frontSlotG M t i j) := by
    intro i j
    have hval := hu _ (coordOfG_frontSlotG_ne_pivot M hL hrs hr hc t ht i j)
    rwa [boxGen_coordOfG] at hval
  constructor
  · -- carrier diagonal `(i:ℕ)=(j:ℕ)<r` ∈ [δ/2,δ]
    intro i j hij hir
    have hmem := hslot i j
    have hbranch : ((frontSlotG M t i j).1.1.val < L - 1 ∧ ((frontSlotG M t i j).1.2.val : ℕ) < r
        ∧ ((frontSlotG M t i j).2.val : ℕ) < r ∧ (frontSlotG M t i j).1.2.val
          = (frontSlotG M t i j).2.val) := by
      refine ⟨ht, ?_, ?_, ?_⟩ <;> simp only [frontSlotG] <;> omega
    rw [slotBoxGen, if_pos hbranch] at hmem
    exact hmem
  · -- every other entry ≤ η
    intro i j hnot
    have hmem := hslot i j
    have hbranch : ¬((frontSlotG M t i j).1.1.val < L - 1 ∧ ((frontSlotG M t i j).1.2.val : ℕ) < r
        ∧ ((frontSlotG M t i j).2.val : ℕ) < r ∧ (frontSlotG M t i j).1.2.val
          = (frontSlotG M t i j).2.val) := by
      simp only [frontSlotG]
      rintro ⟨_, hi, hj, hij⟩
      exact hnot ⟨hij, hi⟩
    rw [slotBoxGen, if_neg hbranch, Set.mem_Icc] at hmem
    rw [abs_le]
    exact hmem

end DLNFibre.DLN.RLCT
