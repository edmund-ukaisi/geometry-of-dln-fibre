import DLNFibre.DLN.RLCT.Validate.RouteMLeafSlotGen
import DLNFibre.DLN.RLCT.Validate.RouteMLeafChart
import DLNFibre.DLN.RLCT.Validate.RouteMLeafBData

/-!
# `RouteMInteriorLiveGenBase` — the general-`L` active-set membership + pbo-fixing readers

The FOUNDATION layer of the general-`L` interior-chart lift (`genm-glift`, task i–iv prerequisites):
the `activeMGen`-membership facts, generalizing the `Fin (2 + 1)`-pinned `activeSlotE_mem_activeM` /
`leafSlot_mem_activeM` / `leafPivot_mem_activeM` (all `RouteMLeafBData` / `RouteMLeafChart`,
boundary-`0`-only).

The structured active set at general `L` is `activeMGen = ⋃_{k : Fin L} activeImgGen k` (banked,
`RouteMLeafSlotGen`): the per-boundary E-block image `activeSlotE k` at interior `k ≠ L−1`, the leaf
image `leafSlot` at `k = L−1`. `activeMGen` contains ONLY E-block + leaf slots. This module establishes
the membership facts:

* `leafPivotGen_mem_activeMGen` — the radial pivot `leafPivot … = leafSlot (L−1) 0 0 ∈ activeMGen`.
* `activeSlotE_mem_activeMGen` / `leafSlot_mem_activeMGen` — per-boundary slot membership.
* `activeSlotE_mem_activeImgGen` / `leafSlot_mem_activeImgGen` — the per-boundary-image versions.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite equivalences; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {L : ℕ}

/-! ## The leaf pivot at general `L` -/

/-- **`leafSlot (L−1) 0 0` IS `leafPivot`** (definitionally, at general `L`). -/
theorem leafSlot_zero_eq_leafPivotGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    leafSlot M (tach M) ha hL ⟨0, h0r⟩ ⟨0, h0c⟩ = leafPivot M ha hL h0r h0c := rfl

/-! ## Membership of a slot in the per-boundary image `activeImgGen`

The banked `activeImgGen M ha k` is the E-block image at interior `k ≠ L−1`, the leaf image at
`k = L−1`. We show the per-boundary slots land in it, hence (via the `biUnion`) in `activeMGen`. -/

/-- The E-block slot `activeSlotE k iE jE` at an interior boundary `k ≠ L−1` lies in
`activeImgGen k`. -/
theorem activeSlotE_mem_activeImgGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1)
    (iE : Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
    (jE : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) :
    activeSlotE M (tach M) ha k iE jE ∈ activeImgGen M ha k := by
  rw [activeImgGen, dif_neg hk, Finset.mem_image]
  exact ⟨(iE, jE), Finset.mem_univ _, rfl⟩

/-- The leaf slot `leafSlot i j` lies in `activeImgGen (L−1)` (the leaf boundary image). -/
theorem leafSlot_mem_activeImgGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (k : Fin L) (hk : k.val = L - 1)
    (i : Fin (Text M (tach M) L)) (j : Fin (Wext M L)) :
    leafSlot M (tach M) ha ha.hL i j ∈ activeImgGen M ha k := by
  rw [activeImgGen, dif_pos hk, Finset.mem_image]
  exact ⟨(i, j), Finset.mem_univ _, rfl⟩

/-! ## Membership in `activeMGen` (the `biUnion`) -/

/-- The E-block slot `activeSlotE k iE jE` at an interior boundary `k ≠ L−1` lies in `activeMGen`. -/
theorem activeSlotE_mem_activeMGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1)
    (iE : Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
    (jE : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) :
    activeSlotE M (tach M) ha k iE jE ∈ activeMGen M ha := by
  rw [activeMGen, Finset.mem_biUnion]
  exact ⟨k, Finset.mem_univ _, activeSlotE_mem_activeImgGen M ha k hk iE jE⟩

/-- The leaf slot `leafSlot i j` lies in `activeMGen`. -/
theorem leafSlot_mem_activeMGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (i : Fin (Text M (tach M) L)) (j : Fin (Wext M L)) :
    leafSlot M (tach M) ha ha.hL i j ∈ activeMGen M ha := by
  have hL : 0 < L := ha.hL
  rw [activeMGen, Finset.mem_biUnion]
  refine ⟨⟨L - 1, by omega⟩, Finset.mem_univ _, ?_⟩
  exact leafSlot_mem_activeImgGen M ha ⟨L - 1, by omega⟩ rfl i j

/-- **`leafPivot ∈ activeMGen`** (general `L`): the radial pivot `p₀ = leafSlot (L−1) 0 0` lies in the
leaf image, hence in `activeMGen`. -/
theorem leafPivotGen_mem_activeMGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    leafPivot M ha hL h0r h0c ∈ activeMGen M ha := by
  rw [← leafSlot_zero_eq_leafPivotGen M ha hL h0r h0c]
  exact leafSlot_mem_activeMGen M ha ⟨0, h0r⟩ ⟨0, h0c⟩

end DLNFibre.DLN.RLCT
