import DLNFibre.DLN.RLCT.Validate.RouteMLeafSlot

/-!
# `RouteMLeafSlotGen` — the general-`L` structured active set + its cardinality `= minAdm`

The general-`L` lift of `RouteMLeafSlot.activeM_card` (which is `Fin (2 + 1)`-pinned). The structured
residual active set for the ∀M interior-det headline at arbitrary depth `L` is the flat coordinates
the radial `u = x p₀` scales: per interior boundary `k = 0 … L−2` the E-block (`activeSlotE`,
`RouteMActiveSlots`), plus the FULL leaf residual at boundary `L − 1` (`leafSlot`, reading the
ChartIdx Schur block at `L − 1`, whose dimension `Text(L)·Wext(L)` matches the leaf).

At `L = 2` there is one interior boundary (`k = 0`) + the leaf (`k = 1`); this recovers the same
per-boundary partition as `RouteMLeafSlot.activeM`. For general `L` the active set is the
disjoint `biUnion` over `k : Fin L` of the per-boundary image, and its cardinality is the Aoyagi
block-sum `∑_k rBlock_k · cBlock_k = minAdm` (`sum_rBlock_cBlock_eq_minAdm`, ∀L).

* `activeImgGen M ha k` — the per-boundary active image: the E-block image (`activeSlotE`) for
  `k ≠ L − 1`, the leaf image (`leafSlot`) for `k = L − 1`.
* `activeImgGen_card` — `card = rBlock_k · cBlock_k` (as ℕ) at every boundary `k` (E-block and leaf
  both, the leaf via `Text(L+1) = 0`).
* `activeImgGen_pairwiseDisjoint` — distinct boundaries `k ≠ k'` read distinct ChartIdx first
  components, so the images are disjoint.
* `activeMGen` — `Finset.univ.biUnion (activeImgGen M ha)`, the structured active set.
* **`activeMGen_card`** — `activeMGen.card = minAdm M` (the disjoint `card_biUnion` sum = the Aoyagi
  block-sum, ∀L).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite equivalences + the banked count; no
analysis). De-risks task (b) of the general-L R1-LOWER interior tide (`genm-glinterior`).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {L : ℕ}

/-! ## The per-boundary active image + its cardinality

At an interior boundary `k ≠ L − 1` the active image is the `activeSlotE` image (the Schur-frame
`u·E` carrier, `rBlock_k × cBlock_k`); at the leaf boundary `k = L − 1` it is the `leafSlot` image
(the leaf residual `Text(L) × Wext(L)`). Both are injective, so the card is the matrix-index product,
which is `rBlock_k · cBlock_k` at every boundary (the leaf via `Text(L+1) = 0`). -/

/-- **The per-boundary active image** at boundary `k : Fin L` — the `activeSlotE` E-block image for
`k ≠ L − 1`, the `leafSlot` leaf image for `k = L − 1`. The general-`L` per-boundary summand of the
structured active set. -/
noncomputable def activeImgGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L) :
    Finset (Fin (routeMAmbient M)) :=
  if hk : k.val = L - 1 then
    Finset.image (fun p : Fin (Text M (tach M) L) × Fin (Wext M L) =>
      leafSlot M (tach M) ha ha.hL p.1 p.2) Finset.univ
  else
    Finset.image (fun p : Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
        × Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2)) =>
      activeSlotE M (tach M) ha k p.1 p.2) Finset.univ

/-- The E-block image card is the matrix-index product `rBlock_k · cBlock_k`
(`(Text(k+1) − Text(k+2)) · (Wext(k+1) − Text(k+2))`), via `activeSlotE` injectivity. -/
theorem activeImgGen_card_interior (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1) :
    (activeImgGen M ha k).card
      = (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
        * (Wext M (k.val + 1) - Text M (tach M) (k.val + 2)) := by
  rw [activeImgGen, dif_neg hk, Finset.card_image_of_injective _ ?_, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  · intro p q hpq
    obtain ⟨hi, hj⟩ := activeSlotE_inj M (tach M) ha k hpq
    exact Prod.ext hi hj

/-- The leaf image card is `Text(L) · Wext(L)`, via `leafSlot` injectivity. -/
theorem activeImgGen_card_leaf (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val = L - 1) :
    (activeImgGen M ha k).card = Text M (tach M) L * Wext M L := by
  rw [activeImgGen, dif_pos hk, Finset.card_image_of_injective _ ?_, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  · intro p q hpq
    obtain ⟨hi, hj⟩ := leafSlot_inj M (tach M) ha ha.hL hpq
    exact Prod.ext hi hj

/-- **The per-boundary card is the Aoyagi block product `rBlock_k · cBlock_k`** at EVERY boundary
`k` (as ℕ). Interior boundaries directly (`rBlock_eq_Text`/`cBlock_eq_Wext`); the leaf via
`Text(L+1) = 0` (`Text_Lsucc_eq_zero`), which turns `Text(L) − Text(L+1) = Text(L)` and
`Wext(L) − Text(L+1) = Wext(L)`. -/
theorem activeImgGen_card (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L) :
    ((activeImgGen M ha k).card : ℤ) = rBlock M k * cBlock M k := by
  by_cases hk : k.val = L - 1
  · rw [activeImgGen_card_leaf M ha k hk, rBlock_eq_Text, cBlock_eq_Wext]
    have hL : 0 < L := ha.hL
    -- `k = L − 1`: `k+1 = L`, `k+2 = L+1`, `Text(L+1) = 0`.
    have hk1 : k.val + 1 = L := by omega
    have hk2 : k.val + 2 = L + 1 := by omega
    have hT0 : Text M (tach M) (k.val + 2) = 0 := by
      rw [hk2]; exact Text_Lsucc_eq_zero M hL
    rw [hk1, hT0]
    have hWL : Wext M L = Wext M (k.val + 1) := by rw [hk1]
    rw [hWL]
    push_cast [Nat.sub_zero]
    ring
  · rw [activeImgGen_card_interior M ha k hk, rBlock_eq_Text, cBlock_eq_Wext]
    -- ℕ subtraction → ℤ: `Text(k+2) ≤ Text(k+1)` (hdesc) and `Text(k+2) ≤ Wext(k+1)` (hub).
    have hle1 : Text M (tach M) (k.val + 2) ≤ Text M (tach M) (k.val + 1) := ha.hdesc k.val k.isLt
    have hle2 : Text M (tach M) (k.val + 2) ≤ Wext M (k.val + 1) := ha.hub k.val
    push_cast [Nat.cast_sub hle1, Nat.cast_sub hle2]
    ring

/-! ## Cross-boundary disjointness

Distinct boundaries read distinct `ChartIdx` first components (the `Σ k : Fin L` tag) under the
injective `chartIdxEquiv.symm`, so the per-boundary images are pairwise disjoint. Both the E-block
(`activeSlotE`) and the leaf (`leafSlot`) place their entry at `chartIdxEquiv.symm ⟨k, …⟩`. -/

/-- The `ChartIdx` first-component (boundary tag) of `activeSlotE M t ha k i j` is `k`. -/
theorem activeSlotE_chartIdx_fst (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L)
    (i : Fin (Text M t (k.val + 1) - Text M t (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) :
    ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL) (activeSlotE M t ha k i j)).1 = k := by
  rw [activeSlotE, Equiv.apply_symm_apply]

/-- The `ChartIdx` first-component (boundary tag) of `leafSlot M t ha hL i j` is `⟨L − 1, _⟩`. -/
theorem leafSlot_chartIdx_fst (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hL : 0 < L)
    (i : Fin (Text M t L)) (j : Fin (Wext M L)) :
    ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL) (leafSlot M t ha hL i j)).1
      = ⟨L - 1, by omega⟩ := by
  rw [leafSlot, Equiv.apply_symm_apply]

/-- **The per-boundary images are pairwise disjoint** — distinct boundaries `k ≠ k'` read distinct
`ChartIdx` first components. Whichever of the two boundaries is the leaf, both the E-block and the
leaf carry their boundary tag as the `ChartIdx` first component, so a shared flat coordinate would
force `k = k'`. -/
theorem activeImgGen_pairwiseDisjoint (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    (↑(Finset.univ : Finset (Fin L)) : Set (Fin L)).PairwiseDisjoint (activeImgGen M ha) := by
  intro k _ k' _ hkk'
  -- the boundary tag `chartIdxEquiv · .1` distinguishes `k` from `k'` on every member of the image.
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro s hsk hsk'
  -- extract the boundary tag of `s` from membership in each image (E-block or leaf).
  have tag : ∀ (m : Fin L), s ∈ activeImgGen M ha m →
      ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL) s).1
        = (if m.val = L - 1 then (⟨L - 1, by omega⟩ : Fin L) else m) := by
    intro m hm
    by_cases hmL : m.val = L - 1
    · rw [activeImgGen, dif_pos hmL, Finset.mem_image] at hm
      obtain ⟨p, _, hp⟩ := hm
      rw [← hp, leafSlot_chartIdx_fst M (tach M) ha ha.hL, if_pos hmL]
    · rw [activeImgGen, dif_neg hmL, Finset.mem_image] at hm
      obtain ⟨p, _, hp⟩ := hm
      rw [← hp, activeSlotE_chartIdx_fst M (tach M) ha m, if_neg hmL]
  have tk := tag k hsk
  have tk' := tag k' hsk'
  rw [tk] at tk'
  -- `tk' : (if k = L−1 then ⟨L−1⟩ else k) = (if k' = L−1 then ⟨L−1⟩ else k')`; force `k = k'`.
  apply hkk'
  by_cases hkL : k.val = L - 1 <;> by_cases hk'L : k'.val = L - 1
  · apply Fin.ext; omega
  · rw [if_pos hkL, if_neg hk'L] at tk'
    -- `tk' : ⟨L−1⟩ = k'` ⟹ `k'.val = L−1`, contradicting `hk'L`.
    exact absurd (congrArg Fin.val tk').symm hk'L
  · rw [if_neg hkL, if_pos hk'L] at tk'
    -- `tk' : k = ⟨L−1⟩` ⟹ `k.val = L−1`, contradicting `hkL`.
    exact absurd (congrArg Fin.val tk') hkL
  · rw [if_neg hkL, if_neg hk'L] at tk'
    exact tk'

/-! ## The structured active set + its cardinality `= minAdm` -/

/-- **The general-`L` structured active set** `activeMGen = ⋃_{k : Fin L} activeImgGen k` — the
disjoint union over all boundaries of the per-boundary active image. -/
noncomputable def activeMGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    Finset (Fin (routeMAmbient M)) :=
  Finset.univ.biUnion (activeImgGen M ha)

/-- **`activeMGen.card = minAdm M`** (∀L): the disjoint `card_biUnion` sum of the per-boundary cards
equals the Aoyagi block-sum `∑_k rBlock_k · cBlock_k = minAdm` (`sum_rBlock_cBlock_eq_minAdm`). The
per-boundary card is `rBlock_k · cBlock_k` at every boundary (`activeImgGen_card`); disjointness is
the distinct boundary tag (`activeImgGen_pairwiseDisjoint`). -/
theorem activeMGen_card (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    (activeMGen M ha).card = minAdm M := by
  rw [activeMGen, Finset.card_biUnion (activeImgGen_pairwiseDisjoint M ha)]
  -- move to ℤ and use the Aoyagi block-sum.
  have hZ : ((∑ k : Fin L, (activeImgGen M ha k).card : ℕ) : ℤ) = (minAdm M : ℤ) := by
    push_cast
    rw [← sum_rBlock_cBlock_eq_minAdm M]
    exact Finset.sum_congr rfl (fun k _ => activeImgGen_card M ha k)
  exact_mod_cast hZ

/-! ## The interior-deepest `(2, 4, 3, 2)` L=3 card instance (the de-risk anchor)

The `genm-l3interior` anchor tuple `(2, 4, 3, 2)` (`L = 3`, `minAdm = 4`, achiever `tStar = (2, 1, 0)`):
its structured active set is the disjoint union over the THREE boundaries — the interior E-block at
`k = 0` (`rBlock·cBlock = 0`, empty), the interior E-block at `k = 1` (`rBlock·cBlock = 2`), and the
leaf at `k = 2` (`rBlock·cBlock = 2`) — totalling `minAdm = 4`. This is the multi-boundary generalization
of `activeM_card_334` (L=2, one interior + leaf); it confirms the general `activeMGen_card` fires on a
genuine L=3 interior-deepest node with the drop SPLIT across two live boundaries. The radial blow-up over
`activeMGen` (card `4`) has pivot-axis Jacobian exponent `minAdm − 1 = 3` — the `|u_p|^{minAdm−1}` weight
the kill-condition names. -/

/-- **The `(2, 4, 3, 2)` L=3 card instance**: `activeMGen (![2,4,3,2]) .card = 4 = minAdm`. The disjoint
`biUnion` over the three boundaries (interior E-blocks `0 + 2` and leaf `2`) has cardinality `minAdm = 4`
— the general `activeMGen_card` on the interior-deepest anchor. `minAdm = 4` by `decide`. -/
theorem activeMGen_card_2432 :
    (activeMGen (![2, 4, 3, 2] : Fin (3 + 1) → ℕ) (structAdm_tach _ (by norm_num))).card = 4 := by
  rw [activeMGen_card]
  rw [← minAdmRec_eq_minAdm]; decide

end DLNFibre.DLN.RLCT
