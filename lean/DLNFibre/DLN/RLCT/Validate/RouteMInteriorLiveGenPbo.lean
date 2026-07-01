import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenBase

/-!
# `RouteMInteriorLiveGenPbo` — the general-`L` `pivotBlowupOn`-fixing K-reader

The general-`L` lift of `RouteMLeafBData.readK_pbo` (boundary-`0`-only) and
`RouteMInteriorLiveContract.readK_pbo_all` (`Fin 2`-pinned): `readK (pbo x) k = readK x k` at EVERY
boundary `k : Fin L`, where `pbo = pivotBlowupOn (activeMGen M ha) (leafPivot M ha …)`.

`pivotBlowupOn active p x q = if q = p then x p else if q ∈ active then x p · x q else x q`. So `pbo`
fixes `q` iff `q ≠ leafPivot ∧ q ∉ activeMGen`. The K-reader coordinate is
`chartIdxEquiv.symm ⟨k, Sum.inl (frameSplitEquiv.symm (Sum.inl (Sum.inl (Sum.inl qK))))⟩` — a
`Sum.inl (Sum.inl (Sum.inl …))` (K-role) frame tag. The `activeMGen` members are E-block slots
(frame tag `Sum.inr …`) and leaf slots (`schurSlotEquiv` tag at boundary `L−1`); at the SAME boundary
the K-role and E-role frame tags differ (`frameSplitEquiv` injective, `inl ≠ inr`), and the leaf
boundary's K-block is `0×0` (`Text(L+1) = 0`), so the K-reader is vacuous there. Hence the K-slot is
never in `activeMGen` nor `= leafPivot`, and `pbo` fixes it.

* `readK_slot_notMem_activeImgGen` — the K-slot at boundary `k` is `∉ activeImgGen k'` for every `k'`.
* `readK_slot_notMem_activeMGen` — hence `∉ activeMGen`.
* `readK_slot_ne_leafPivot` — the K-slot is `≠ leafPivot`.
* `readK_pbo_all` — `readK (pbo x) k = readK x k` ∀`k : Fin L`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite equivalences; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {L : ℕ}

/-- The K-reader flat coordinate at boundary `k`, index `(i, j)`: the `readK` slot
`chartIdxEquiv.symm ⟨k, Sum.inl (frameSplitEquiv.symm (Sum.inl (Sum.inl (Sum.inl (finProd (i,j))))))⟩`. -/
noncomputable def readKslot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (i j : Fin (Text M (tach M) (k.val + 2))) : Fin (routeMAmbient M) :=
  (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
    ⟨k, Sum.inl ((frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val)).symm
      (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (i, j))))))⟩

/-- `readK x k i j = x (readKslot k i j)` (the reader IS the coordinate read). -/
theorem readK_eq_readKslot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (x : Fin (routeMAmbient M) → ℝ) (i j : Fin (Text M (tach M) (k.val + 2))) :
    readK M (tach M) ha x k i j = x (readKslot M ha k i j) := rfl

/-- **The K-slot at boundary `k` is `∉ activeImgGen k'`** for every `k'`. If `k' ≠ k`, the chartIdx
boundary tags differ. If `k' = k` and `k'` is interior, the E-image frame tag is a `Sum.inr` where the
K-slot is `Sum.inl (Sum.inl (Sum.inl …))` (distinct under `frameSplitEquiv` injectivity). If `k' = k`
is the leaf boundary, the K-index type `Fin (Text (k+2) · Text (k+2))` is empty (`Text(L+1) = 0`), so
there is no such K-slot. -/
theorem readKslot_notMem_activeImgGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (i j : Fin (Text M (tach M) (k.val + 2))) (k' : Fin L) :
    readKslot M ha k i j ∉ activeImgGen M ha k' := by
  by_cases hk' : k'.val = L - 1
  · -- leaf-image at `k'`: elements are `leafSlot i' j'` at boundary `L−1`.
    rw [activeImgGen, dif_pos hk', Finset.mem_image]
    rintro ⟨p, _, hp⟩
    rw [readKslot, leafSlot] at hp
    have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective hp
    rw [Sigma.mk.inj_iff] at h2
    -- boundary tags: `⟨L−1⟩ = k`.  At `k = L − 1`, `Text (k+2) = 0`, so the K-index `i` is impossible.
    have hkval : k.val = L - 1 := (congrArg Fin.val h2.1).symm
    have hL : 0 < L := ha.hL
    have hi0 : Text M (tach M) (k.val + 2) = 0 := by
      have hk2 : k.val + 2 = L + 1 := by omega
      rw [hk2]; exact Text_Lsucc_eq_zero M hL
    have := i.isLt; omega
  · -- E-image at `k'`: elements are `activeSlotE k' iE jE`.
    rw [activeImgGen, dif_neg hk', Finset.mem_image]
    rintro ⟨p, _, hp⟩
    rw [readKslot, activeSlotE] at hp
    have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective hp
    rw [Sigma.mk.inj_iff] at h2
    -- boundary tags equal ⟹ `k' = k`; then the frame tags: E `Sum.inr` vs K `Sum.inl (Sum.inl (Sum.inl))`.
    have hkeq : k' = k := h2.1
    subst hkeq
    have htag := h2.2
    simp only [heq_eq_eq, Sum.inl.injEq] at htag
    have hfse := (frameSplitEquiv M (tach M) (k'.val + 1) (ha.hdesc k'.val k'.isLt)
      (ha.hub k'.val)).symm.injective htag
    exact Sum.inl_ne_inr hfse.symm

/-- **The K-slot at boundary `k` is `∉ activeMGen`** (it is in no per-boundary image). -/
theorem readKslot_notMem_activeMGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (i j : Fin (Text M (tach M) (k.val + 2))) :
    readKslot M ha k i j ∉ activeMGen M ha := by
  rw [activeMGen, Finset.mem_biUnion, not_exists]
  intro k'
  rw [not_and]
  exact fun _ => readKslot_notMem_activeImgGen M ha k i j k'

/-- **The K-slot at boundary `k` is `≠ leafPivot`** (the leaf pivot is a leaf slot; the K-slot is a
frame `Sum.inl (Sum.inl (Sum.inl …))` tag, and the leaf slot decode is a `schurSlotEquiv` tag at
boundary `L−1`). At `k = L−1` the K-index type is empty; else the boundary tags differ. -/
theorem readKslot_ne_leafPivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (k : Fin L)
    (i j : Fin (Text M (tach M) (k.val + 2))) :
    readKslot M ha k i j ≠ leafPivot M ha hL h0r h0c := by
  rw [← leafSlot_zero_eq_leafPivotGen M ha hL h0r h0c]
  intro h
  rw [readKslot, leafSlot] at h
  have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective h
  rw [Sigma.mk.inj_iff] at h2
  have hkval : k.val = L - 1 := congrArg Fin.val h2.1
  have hi0 : Text M (tach M) (k.val + 2) = 0 := by
    have hk2 : k.val + 2 = L + 1 := by omega
    rw [hk2]; exact Text_Lsucc_eq_zero M hL
  have := i.isLt; omega

/-- **`readK (pbo x) k = readK x k` at EVERY boundary `k : Fin L`** — the general-`L` `readK_pbo_all`.
The K-slot is `≠ leafPivot` and `∉ activeMGen`, so `pivotBlowupOn` fixes it. -/
theorem readK_pbo_all (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) (i j : Fin (Text M (tach M) (k.val + 2))) :
    readK M (tach M) ha
        (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x) k i j
      = readK M (tach M) ha x k i j := by
  rw [readK_eq_readKslot, readK_eq_readKslot, pivotBlowupOn,
    if_neg (readKslot_ne_leafPivot M ha hL h0r h0c k i j),
    if_neg (readKslot_notMem_activeMGen M ha k i j)]

end DLNFibre.DLN.RLCT
