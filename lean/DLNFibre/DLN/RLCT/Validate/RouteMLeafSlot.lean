import DLNFibre.DLN.RLCT.Validate.RouteMActiveSlots
import DLNFibre.DLN.RLCT.Validate.RouteMReaderCard
import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanMinAdm

/-!
# `RouteMLeafSlot` — the leaf-residual flat-slot embedding + the structured `active M` (∀M-L2)

The structured residual active set for the ∀M interior-det headline at `L = 2` is the set of flat
coordinates the radial `u = x p₀` scales: the single interior boundary's E-block (`activeSlotE`,
`RouteMActiveSlots`) plus the FULL leaf residual `Rfin L : Text L × Wext L`. The cert addendum
flagged the leaf-slot routing as the one open sub-design ("the leaf must reuse the slot the dead
`Rmat L` wastes, at a LARGER dimension").

The resolution (this module): the leaf reads the chart-coordinate **Schur block at ChartIdx
boundary `L − 1`** — whose dimension `schurDim (L−1) = tDesc(L−1)·Wext(L) = Text(L)·Wext(L)`
matches the leaf size `Text(L) × Wext(L)`. The interior decoder's `Bmat L`/`Nblk L` etc. (read from
this slot via the `k+1` arm at `k = L−1`) are OVERRIDDEN by the leaf arm `Cgen L = u·Rfin`, so this
Schur block is free for the leaf. At `L = 2` the interior E-block (ChartIdx boundary `0`) and the
leaf (ChartIdx boundary `1`) sit at DISTINCT boundaries, disjoint by `chartIdxEquiv` injectivity.

* `leafSlot` — the leaf flat-slot embedding (the ChartIdx boundary-`(L−1)` Schur slot), injective in
  `(i, j)`.
* `leafSlot_inj` — injectivity.
* `activeM` (L = 2) — `(image of activeSlotE at the interior boundary) ∪ (image of leafSlot)`.
* `activeM_card` — `activeM.card = minAdm M` (disjoint `card_union`: `rBlock·cBlock` plus the leaf
  `Text(2)·Wext(2)`, the latter `= rBlock(1)·cBlock(1)` since `tStar (last) = 0`).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite equivalences + the banked count; no
analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {L : ℕ}

/-! ## The leaf-residual flat-slot embedding -/

/-- **The leaf flat-slot embedding** — the flat coordinate carrying the leaf residual entry `(i, j)`
(`Text L × Wext L`). Reads the ChartIdx **Schur block** at boundary `L − 1`, whose dimension
`schurDim (L−1) = tDesc (L−1) · Wext L = Text L · Wext L` matches the leaf size. The decoder's
`Bmat L`/`Nblk L` read from this slot are overridden by the leaf arm `Cgen L = u·Rfin`. -/
noncomputable def leafSlot (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hL : 0 < L)
    (i : Fin (Text M t L)) (j : Fin (Wext M L)) : Fin (routeMAmbient M) :=
  (chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm
    ⟨⟨L - 1, by omega⟩,
      Sum.inl ((schurSlotEquiv M (tDesc M t) (L - 1)).symm
        (Fin.cast (show Text M t L = tDesc M t (L - 1) by
          rw [tDesc_apply]; congr 1; omega) i,
         Fin.cast (show Wext M L = Wext M (L - 1 + 1) by congr 1; omega) j))⟩

/-- **`leafSlot` is injective in the matrix index `(i, j)`** — distinct leaf entries occupy distinct
flat slots. Composition of the injective `chartIdxEquiv.symm`, `schurSlotEquiv.symm`, `Fin.cast`. -/
theorem leafSlot_inj (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hL : 0 < L)
    {i i' : Fin (Text M t L)} {j j' : Fin (Wext M L)}
    (h : leafSlot M t ha hL i j = leafSlot M t ha hL i' j') : i = i' ∧ j = j' := by
  unfold leafSlot at h
  have h2 := (chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm.injective h
  rw [Sigma.mk.inj_iff] at h2
  have h3 := h2.2
  simp only [heq_eq_eq, Sum.inl.injEq] at h3
  have h4 := (schurSlotEquiv M (tDesc M t) (L - 1)).symm.injective h3
  rw [Prod.mk.injEq] at h4
  refine ⟨?_, ?_⟩
  · exact Fin.cast_injective _ h4.1
  · exact Fin.cast_injective _ h4.2

/-- The leaf slot and an E-block slot at a DISTINCT ChartIdx boundary read distinct flat coords
(distinct Sigma first components under the injective `chartIdxEquiv.symm`). -/
theorem leafSlot_ne_activeSlotE (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hL : 0 < L)
    (k : Fin L) (hk : k.val ≠ L - 1)
    (i : Fin (Text M t L)) (j : Fin (Wext M L))
    (iE : Fin (Text M t (k.val + 1) - Text M t (k.val + 2)))
    (jE : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) :
    leafSlot M t ha hL i j ≠ activeSlotE M t ha k iE jE := by
  intro h
  unfold leafSlot activeSlotE at h
  have h2 := (chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm.injective h
  rw [Sigma.mk.inj_iff] at h2
  have h1 : (⟨L - 1, by omega⟩ : Fin L) = k := h2.1
  exact hk (by rw [← h1])

/-! ## The structured `active` set at `L = 2` + its cardinality `= minAdm`

At `L = 2` there is exactly ONE interior boundary (ChartIdx boundary `0`, GenBlk `s = 1`) carrying a
nonzero E-block, plus the leaf (boundary `1`). The active set is the image of `activeSlotE` at the
interior boundary together with the image of `leafSlot`. The two images are disjoint (distinct
ChartIdx boundaries `0 ≠ 1 = L − 1`), so the cardinality is the sum of the two products, which
equals `minAdm` by the Aoyagi bridge (`rBlock·cBlock` sum) plus `tStar (last) = 0` (the leaf product
is the last Aoyagi block). -/

variable {M : Fin (2 + 1) → ℕ}

/-- The E-block image at the interior boundary `⟨0⟩` (`Fin L = Fin 2`). -/
noncomputable def activeEImg (M : Fin (2 + 1) → ℕ) (ha : StructAdm M (tach M)) :
    Finset (Fin (routeMAmbient M)) :=
  Finset.image (fun p : Fin (Text M (tach M) 1 - Text M (tach M) 2)
      × Fin (Wext M 1 - Text M (tach M) 2) =>
    activeSlotE M (tach M) ha ⟨0, by decide⟩
      (Fin.cast (by norm_num) p.1) (Fin.cast (by norm_num) p.2)) Finset.univ

/-- The leaf image (`Fin (Text 2) × Fin (Wext 2)`). -/
noncomputable def activeLeafImg (M : Fin (2 + 1) → ℕ) (ha : StructAdm M (tach M)) :
    Finset (Fin (routeMAmbient M)) :=
  Finset.image (fun p : Fin (Text M (tach M) 2) × Fin (Wext M 2) =>
    leafSlot M (tach M) ha (by norm_num) p.1 p.2) Finset.univ

/-- **The structured active set** `activeM = activeEImg ∪ activeLeafImg` for `L = 2`. -/
noncomputable def activeM (M : Fin (2 + 1) → ℕ) (ha : StructAdm M (tach M)) :
    Finset (Fin (routeMAmbient M)) :=
  activeEImg M ha ∪ activeLeafImg M ha

/-- `activeEImg.card = (Text 1 − Text 2)·(Wext 1 − Text 2)` (injective `activeSlotE` at `⟨0⟩`). -/
theorem activeEImg_card (ha : StructAdm M (tach M)) :
    (activeEImg M ha).card
      = (Text M (tach M) 1 - Text M (tach M) 2) * (Wext M 1 - Text M (tach M) 2) := by
  rw [activeEImg, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  · intro p q hpq
    obtain ⟨hi, hj⟩ := activeSlotE_inj M (tach M) ha ⟨0, by decide⟩ hpq
    have h1 : p.1 = q.1 := Fin.cast_injective _ hi
    have h2 : p.2 = q.2 := Fin.cast_injective _ hj
    exact Prod.ext h1 h2

/-- `activeLeafImg.card = Text 2 · Wext 2` (injective `leafSlot`). -/
theorem activeLeafImg_card (ha : StructAdm M (tach M)) :
    (activeLeafImg M ha).card = Text M (tach M) 2 * Wext M 2 := by
  rw [activeLeafImg, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  · intro p q hpq
    obtain ⟨hi, hj⟩ := leafSlot_inj M (tach M) ha (by norm_num) hpq
    exact Prod.ext hi hj

/-- The E-image and the leaf-image are disjoint (distinct ChartIdx boundaries `0 ≠ 1 = L − 1`). -/
theorem activeEImg_disjoint_activeLeafImg (ha : StructAdm M (tach M)) :
    Disjoint (activeEImg M ha) (activeLeafImg M ha) := by
  rw [Finset.disjoint_left]
  rintro s hsE hsL
  rw [activeEImg, Finset.mem_image] at hsE
  rw [activeLeafImg, Finset.mem_image] at hsL
  obtain ⟨pE, _, hpE⟩ := hsE
  obtain ⟨pL, _, hpL⟩ := hsL
  apply leafSlot_ne_activeSlotE M (tach M) ha (by norm_num) ⟨0, by decide⟩ (by decide)
    pL.1 pL.2 (Fin.cast (by norm_num) pE.1) (Fin.cast (by norm_num) pE.2)
  rw [hpL, hpE]

/-- **`activeM.card = minAdm M`** (`L = 2`): disjoint union, `(Text 1 − Text 2)·(Wext 1 − Text 2)`
(the interior E-block, `= rBlock 0 · cBlock 0`) plus `Text 2 · Wext 2` (the leaf, equal to
`rBlock 1 · cBlock 1` since `tStar (last) = 0`), summing to `minAdm` via the Aoyagi bridge. -/
theorem activeM_card (ha : StructAdm M (tach M)) :
    (activeM M ha).card = minAdm M := by
  rw [activeM, Finset.card_union_of_disjoint (activeEImg_disjoint_activeLeafImg ha),
    activeEImg_card ha, activeLeafImg_card ha]
  -- the two products are `rBlock 0 · cBlock 0` and `rBlock 1 · cBlock 1` (over ℤ via the bridge)
  have hsum := sum_rBlock_cBlock_eq_minAdm M
  rw [Fin.sum_univ_two] at hsum
  -- block 0: rBlock 0 · cBlock 0 = (Text 1 − Text 2)·(Wext 1 − Text 2)
  have hr0 : rBlock M (0 : Fin 2)
      = (Text M (tach M) 1 : ℤ) - (Text M (tach M) 2 : ℤ) := by
    rw [rBlock_eq_Text]; norm_num
  have hc0 : cBlock M (0 : Fin 2)
      = (Wext M 1 : ℤ) - (Text M (tach M) 2 : ℤ) := by
    rw [cBlock_eq_Wext]; norm_num
  -- block 1: rBlock 1 · cBlock 1 = Text 2 · Wext 2 (Text 3 = 0 since tStar last = 0)
  have hT3 : Text M (tach M) 3 = 0 := by
    have := Text_Lsucc_eq_zero M (by norm_num : 0 < 2)
    simpa using this
  have hr1 : rBlock M (1 : Fin 2) = (Text M (tach M) 2 : ℤ) := by
    rw [rBlock_eq_Text]
    rw [show ((1 : Fin 2).val) + 1 = 2 from rfl, show ((1 : Fin 2).val) + 2 = 3 from rfl, hT3]
    push_cast; ring
  have hc1 : cBlock M (1 : Fin 2) = (Wext M 2 : ℤ) := by
    rw [cBlock_eq_Wext]
    rw [show ((1 : Fin 2).val) + 1 = 2 from rfl, show ((1 : Fin 2).val) + 2 = 3 from rfl, hT3]
    push_cast; ring
  -- assemble over ℤ then cast back
  have hZ : ((Text M (tach M) 1 - Text M (tach M) 2) * (Wext M 1 - Text M (tach M) 2)
        + Text M (tach M) 2 * Wext M 2 : ℤ) = (minAdm M : ℤ) := by
    rw [← hsum, hr0, hc0, hr1, hc1]
  -- ℕ subtraction → ℤ: Text 2 ≤ Text 1 and Text 2 ≤ Wext 1 (the descent admissibility)
  have hle1 : Text M (tach M) 2 ≤ Text M (tach M) 1 := by
    have := ha.hdesc 0 (by norm_num); simpa using this
  have hle2 : Text M (tach M) 2 ≤ Wext M 1 := by
    have := ha.hub 0; simpa using this
  have hcast : (((Text M (tach M) 1 - Text M (tach M) 2) * (Wext M 1 - Text M (tach M) 2)
        + Text M (tach M) 2 * Wext M 2 : ℕ) : ℤ)
      = ((Text M (tach M) 1 : ℤ) - (Text M (tach M) 2 : ℤ))
          * ((Wext M 1 : ℤ) - (Text M (tach M) 2 : ℤ))
        + (Text M (tach M) 2 : ℤ) * (Wext M 2 : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hle1, Nat.cast_sub hle2]
  rw [← Nat.cast_inj (R := ℤ), hcast, hZ]

/-! ## VALIDATE-SMALL (3,3,4) — the binding gate

`M334 = ![3,3,4]` has `minAdm = 8`. The structured active set `activeM M334` is the disjoint union
of the interior E-block (`2×2 = 4` for `(3,3,4)`: `tach = (3, tStar0, 0)`, `tStar0 = 1`, so
`(Text 1 − Text 2)·(Wext 1 − Text 2) = (3−1)·(3−1) = 4`) and the leaf (`Text 2 · Wext 2 = 1·4 = 4`),
totalling `8 = minAdm`. This `activeM_card`-instance is the structural confirmation the design pin
predicted: `active.card = minAdm = 8`, with the radial exponent `minAdm − 1 = 7` matching the
HONEST `(3,3,4)` chart's `leafH334 0 = 7` (`RouteMLayerCoverGEL2`). The gate PASSES. -/

/-- **The (3,3,4) gate**: `activeM (![3,3,4]) .card = 8 = minAdm (![3,3,4])` — the genBlkFlatLive +
leaf-pivot active set has cardinality `minAdm = 8`, confirming the design pin (interior E-block `4`
plus leaf `4`). The card identity is the abstract `activeM_card`; `minAdm = 8` is by `decide`. -/
theorem activeM_card_334 :
    (activeM (![3, 3, 4] : Fin (2 + 1) → ℕ) (structAdm_tach _ (by norm_num))).card = 8 := by
  rw [activeM_card]
  decide

end DLNFibre.DLN.RLCT
