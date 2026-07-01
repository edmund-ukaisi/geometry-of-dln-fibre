import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenPbo

/-!
# `RouteMInteriorLiveGenChart` — the general-`L` interior-chart pbo-fixing X/N readers + E-scaling

The X/N/E-reader layer of the general-`L` interior-chart lift (`genm-glift`), generalizing the
`Fin (2 + 1)`-pinned `readX_pbo` / `readN_pbo` / `readE_pbo` of `RouteMLeafBData` (boundary-`0`-only)
to EVERY interior boundary `k : Fin L`.

`pivotBlowupOn active p x q = if q = p then x p else if q ∈ active then x p · x q else x q`. The X/N
readers place their entry at a frame `Sum.inl (frameSplitEquiv.symm (Sum.inl (Sum.inl (Sum.inr …))))`
(X) / `Sum.inl (frameSplitEquiv.symm (Sum.inl (Sum.inr …)))` (N) tag — distinct from the E-tag
`Sum.inl (frameSplitEquiv.symm (Sum.inr …))` and the leaf `schurSlotEquiv` tag — so `pbo` FIXES them.
The E-reader slot at an interior boundary `k ≠ L−1` IS `activeSlotE k i j ∈ activeMGen`, `≠ leafPivot`,
so `pbo` SCALES it by `x leafPivot`. (The X/N/E readers at the leaf boundary `k = L−1` are vacuous —
`Text(L+1) = 0` empties the K-width; but X/N/E have other widths, so they are stated at interior `k`.)

The decode mirrors `RouteMInteriorLiveGenPbo.readKslot_notMem_activeMGen` EXACTLY (the
`chartIdxEquiv.symm.injective` + `Sigma.mk.inj_iff` + `frameSplitEquiv.symm.injective` +
`Sum.inl_ne_inr` route; the leaf boundary vacuous by boundary-tag mismatch).

* `readXslot` / `readNslot` — the flat coordinate the X- / N-reader reads.
* `readX_pbo_all` / `readN_pbo_all` — `read? (pbo x) k = read? x k` at EVERY interior boundary `k ≠ L−1`.
* `readE_pbo_all` — `readE (pbo x) k = (x leafPivot)·readE x k` at EVERY interior boundary `k ≠ L−1`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite equivalences; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {L : ℕ}

/-! ## The X- / N-reader flat coordinates -/

/-- The X-reader flat coordinate at boundary `k`, index `(i, j)`: the X-tag
`Sum.inl (frameSplitEquiv.symm (Sum.inl (Sum.inl (Sum.inr (finProd (i,j))))))`. -/
noncomputable def readXslot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (i : Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
    (j : Fin (Text M (tach M) (k.val + 2))) : Fin (routeMAmbient M) :=
  (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
    ⟨k, Sum.inl ((frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val)).symm
      (Sum.inl (Sum.inl (Sum.inr (finProdFinEquiv (i, j))))))⟩

/-- `readX x k i j = x (readXslot k i j)`. -/
theorem readX_eq_readXslot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (x : Fin (routeMAmbient M) → ℝ) (i : Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
    (j : Fin (Text M (tach M) (k.val + 2))) :
    readX M (tach M) ha x k i j = x (readXslot M ha k i j) := rfl

/-- The N-reader flat coordinate at boundary `k`, index `(i, j)`: the N-tag
`Sum.inl (frameSplitEquiv.symm (Sum.inl (Sum.inr (finProd (i,j)))))`. -/
noncomputable def readNslot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (i : Fin (Text M (tach M) (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) : Fin (routeMAmbient M) :=
  (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
    ⟨k, Sum.inl ((frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val)).symm
      (Sum.inl (Sum.inr (finProdFinEquiv (i, j)))))⟩

/-- `readN x k i j = x (readNslot k i j)`. -/
theorem readN_eq_readNslot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (x : Fin (routeMAmbient M) → ℝ) (i : Fin (Text M (tach M) (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) :
    readN M (tach M) ha x k i j = x (readNslot M ha k i j) := rfl

/-! ## The X-slot is fixed by `pivotBlowupOn` (not in `activeMGen`, `≠ leafPivot`) -/

/-- **The X-slot at boundary `k` is `∉ activeImgGen k'`** for every `k'`. Mirrors
`readKslot_notMem_activeImgGen`: leaf-image at `k'` (`k' = L−1`) forces the boundary tag `k = L−1`,
then the frame tag is a `schurSlotEquiv` decode vs the X-tag `Sum.inl (Sum.inl (Sum.inr …))` — but
the leaf case is handled by the boundary tag equality forcing the X frame tag to equal the leaf's
`schurSlotEquiv` tag; the E-image at `k'` forces `k' = k`, then E-tag `Sum.inr` vs X-tag `Sum.inl …`. -/
theorem readXslot_notMem_activeImgGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1)
    (i : Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
    (j : Fin (Text M (tach M) (k.val + 2))) (k' : Fin L) :
    readXslot M ha k i j ∉ activeImgGen M ha k' := by
  by_cases hk' : k'.val = L - 1
  · -- leaf-image at `k'`: elements are `leafSlot i' j'` at boundary `L − 1`.
    rw [activeImgGen, dif_pos hk', Finset.mem_image]
    rintro ⟨p, _, hp⟩
    rw [readXslot, leafSlot] at hp
    have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective hp
    rw [Sigma.mk.inj_iff] at h2
    -- boundary tags: `⟨L−1⟩ = k` ⟹ `k = L − 1`, contradicting `hk`.
    have hkval : k.val = L - 1 := (congrArg Fin.val h2.1).symm
    exact hk hkval
  · -- E-image at `k'`: elements are `activeSlotE k' iE jE`.
    rw [activeImgGen, dif_neg hk', Finset.mem_image]
    rintro ⟨p, _, hp⟩
    rw [readXslot, activeSlotE] at hp
    have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective hp
    rw [Sigma.mk.inj_iff] at h2
    have hkeq : k' = k := h2.1
    subst hkeq
    have htag := h2.2
    simp only [heq_eq_eq, Sum.inl.injEq] at htag
    have hfse := (frameSplitEquiv M (tach M) (k'.val + 1) (ha.hdesc k'.val k'.isLt)
      (ha.hub k'.val)).symm.injective htag
    exact Sum.inl_ne_inr hfse.symm

/-- **The X-slot at boundary `k` is `∉ activeMGen`**. -/
theorem readXslot_notMem_activeMGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1)
    (i : Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
    (j : Fin (Text M (tach M) (k.val + 2))) :
    readXslot M ha k i j ∉ activeMGen M ha := by
  rw [activeMGen, Finset.mem_biUnion, not_exists]
  intro k'
  rw [not_and]
  exact fun _ => readXslot_notMem_activeImgGen M ha k hk i j k'

/-- **The X-slot at boundary `k` is `≠ leafPivot`** (the leaf pivot is a leaf slot at boundary `L−1`;
the X-slot boundary tag is `k ≠ L−1`). -/
theorem readXslot_ne_leafPivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (k : Fin L) (hk : k.val ≠ L - 1)
    (i : Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
    (j : Fin (Text M (tach M) (k.val + 2))) :
    readXslot M ha k i j ≠ leafPivot M ha hL h0r h0c := by
  rw [← leafSlot_zero_eq_leafPivotGen M ha hL h0r h0c]
  intro h
  rw [readXslot, leafSlot] at h
  have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective h
  rw [Sigma.mk.inj_iff] at h2
  have hkval : k.val = L - 1 := congrArg Fin.val h2.1
  exact hk hkval

/-- **`readX (pbo x) k = readX x k` at EVERY interior boundary `k ≠ L−1`** — the X-slot is
`≠ leafPivot` and `∉ activeMGen`, so `pivotBlowupOn` fixes it. -/
theorem readX_pbo_all (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) (hk : k.val ≠ L - 1)
    (i : Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
    (j : Fin (Text M (tach M) (k.val + 2))) :
    readX M (tach M) ha
        (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x) k i j
      = readX M (tach M) ha x k i j := by
  rw [readX_eq_readXslot, readX_eq_readXslot, pivotBlowupOn,
    if_neg (readXslot_ne_leafPivot M ha hL h0r h0c k hk i j),
    if_neg (readXslot_notMem_activeMGen M ha k hk i j)]

/-! ## The N-slot is fixed by `pivotBlowupOn` -/

/-- **The N-slot at boundary `k` is `∉ activeImgGen k'`** for every `k'`. -/
theorem readNslot_notMem_activeImgGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1)
    (i : Fin (Text M (tach M) (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) (k' : Fin L) :
    readNslot M ha k i j ∉ activeImgGen M ha k' := by
  by_cases hk' : k'.val = L - 1
  · rw [activeImgGen, dif_pos hk', Finset.mem_image]
    rintro ⟨p, _, hp⟩
    rw [readNslot, leafSlot] at hp
    have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective hp
    rw [Sigma.mk.inj_iff] at h2
    have hkval : k.val = L - 1 := (congrArg Fin.val h2.1).symm
    exact hk hkval
  · rw [activeImgGen, dif_neg hk', Finset.mem_image]
    rintro ⟨p, _, hp⟩
    rw [readNslot, activeSlotE] at hp
    have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective hp
    rw [Sigma.mk.inj_iff] at h2
    have hkeq : k' = k := h2.1
    subst hkeq
    have htag := h2.2
    simp only [heq_eq_eq, Sum.inl.injEq] at htag
    have hfse := (frameSplitEquiv M (tach M) (k'.val + 1) (ha.hdesc k'.val k'.isLt)
      (ha.hub k'.val)).symm.injective htag
    exact Sum.inl_ne_inr hfse.symm

/-- **The N-slot at boundary `k` is `∉ activeMGen`**. -/
theorem readNslot_notMem_activeMGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1)
    (i : Fin (Text M (tach M) (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) :
    readNslot M ha k i j ∉ activeMGen M ha := by
  rw [activeMGen, Finset.mem_biUnion, not_exists]
  intro k'
  rw [not_and]
  exact fun _ => readNslot_notMem_activeImgGen M ha k hk i j k'

/-- **The N-slot at boundary `k` is `≠ leafPivot`**. -/
theorem readNslot_ne_leafPivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (k : Fin L) (hk : k.val ≠ L - 1)
    (i : Fin (Text M (tach M) (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) :
    readNslot M ha k i j ≠ leafPivot M ha hL h0r h0c := by
  rw [← leafSlot_zero_eq_leafPivotGen M ha hL h0r h0c]
  intro h
  rw [readNslot, leafSlot] at h
  have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective h
  rw [Sigma.mk.inj_iff] at h2
  have hkval : k.val = L - 1 := congrArg Fin.val h2.1
  exact hk hkval

/-- **`readN (pbo x) k = readN x k` at EVERY interior boundary `k ≠ L−1`**. -/
theorem readN_pbo_all (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) (hk : k.val ≠ L - 1)
    (i : Fin (Text M (tach M) (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) :
    readN M (tach M) ha
        (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x) k i j
      = readN M (tach M) ha x k i j := by
  rw [readN_eq_readNslot, readN_eq_readNslot, pivotBlowupOn,
    if_neg (readNslot_ne_leafPivot M ha hL h0r h0c k hk i j),
    if_neg (readNslot_notMem_activeMGen M ha k hk i j)]

/-! ## The W-slot (lift role) is fixed by `pivotBlowupOn` -/

/-- The W-reader flat coordinate at boundary `k`, index `(i, j)`: the lift-tag
`Sum.inr (liftSlotEquiv.symm (i, j))` (the chartIdx-fiber `Sum.inr` summand). -/
noncomputable def readWslot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val + 1 < L)
    (i : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) (j : Fin (Wext M (k.val + 2))) :
    Fin (routeMAmbient M) :=
  (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
    ⟨k, Sum.inr ((liftSlotEquiv M (tDesc M (tach M)) k.val hk).symm (i, j))⟩

/-- `readW x k hk i j = x (readWslot k hk i j)`. -/
theorem readW_eq_readWslot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val + 1 < L) (x : Fin (routeMAmbient M) → ℝ)
    (i : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) (j : Fin (Wext M (k.val + 2))) :
    readW M (tach M) ha x k hk i j = x (readWslot M ha k hk i j) := rfl

/-- **The W-slot at boundary `k` is `∉ activeImgGen k'`** for every `k'` — the W-tag is the chartIdx
`Sum.inr` (lift) summand, whereas both the E-image and leaf-image tags are `Sum.inl` (frame). -/
theorem readWslot_notMem_activeImgGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val + 1 < L)
    (i : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) (j : Fin (Wext M (k.val + 2)))
    (k' : Fin L) :
    readWslot M ha k hk i j ∉ activeImgGen M ha k' := by
  by_cases hk' : k'.val = L - 1
  · rw [activeImgGen, dif_pos hk', Finset.mem_image]
    rintro ⟨p, _, hp⟩
    rw [readWslot, leafSlot] at hp
    have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective hp
    rw [Sigma.mk.inj_iff] at h2
    obtain ⟨hb, htag⟩ := h2
    subst hb
    simp only [heq_eq_eq] at htag
    exact Sum.inl_ne_inr htag
  · rw [activeImgGen, dif_neg hk', Finset.mem_image]
    rintro ⟨p, _, hp⟩
    rw [readWslot, activeSlotE] at hp
    have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective hp
    rw [Sigma.mk.inj_iff] at h2
    obtain ⟨hb, htag⟩ := h2
    subst hb
    simp only [heq_eq_eq] at htag
    exact Sum.inl_ne_inr htag

/-- **The W-slot at boundary `k` is `∉ activeMGen`**. -/
theorem readWslot_notMem_activeMGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val + 1 < L)
    (i : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) (j : Fin (Wext M (k.val + 2))) :
    readWslot M ha k hk i j ∉ activeMGen M ha := by
  rw [activeMGen, Finset.mem_biUnion, not_exists]
  intro k'
  rw [not_and]
  exact fun _ => readWslot_notMem_activeImgGen M ha k hk i j k'

/-- **The W-slot at boundary `k` is `≠ leafPivot`** (the leaf pivot is a frame `Sum.inl` slot; the
W-slot is a lift `Sum.inr` slot). -/
theorem readWslot_ne_leafPivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (k : Fin L) (hk : k.val + 1 < L)
    (i : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) (j : Fin (Wext M (k.val + 2))) :
    readWslot M ha k hk i j ≠ leafPivot M ha hL h0r h0c := by
  rw [← leafSlot_zero_eq_leafPivotGen M ha hL h0r h0c]
  intro h
  rw [readWslot, leafSlot] at h
  have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective h
  rw [Sigma.mk.inj_iff] at h2
  obtain ⟨hb, htag⟩ := h2
  subst hb
  simp only [heq_eq_eq] at htag
  exact Sum.inr_ne_inl htag

/-- **`readW (pbo x) k = readW x k` at EVERY interior boundary with a lift (`k.val + 1 < L`)**. -/
theorem readW_pbo_all (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) (hk : k.val + 1 < L)
    (i : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) (j : Fin (Wext M (k.val + 2))) :
    readW M (tach M) ha
        (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x) k hk i j
      = readW M (tach M) ha x k hk i j := by
  rw [readW_eq_readWslot, readW_eq_readWslot, pivotBlowupOn,
    if_neg (readWslot_ne_leafPivot M ha hL h0r h0c k hk i j),
    if_neg (readWslot_notMem_activeMGen M ha k hk i j)]

/-! ## The E-slot SCALES under `pivotBlowupOn` (it IS `activeSlotE ∈ activeMGen`) -/

/-- **`readE (pbo x) k = (x leafPivot)·readE x k` at EVERY interior boundary `k ≠ L−1`** — the E-slot
at `k i j` IS `activeSlotE k i j`, in `activeMGen` (`activeSlotE_mem_activeMGen`) and `≠ leafPivot`, so
`pivotBlowupOn` scales it. The radial-scaling kernel of the E-block match. -/
theorem readE_pbo_all (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) (hk : k.val ≠ L - 1)
    (i : Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) :
    readE M (tach M) ha
        (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x) k i j
      = x (leafPivot M ha hL h0r h0c) * readE M (tach M) ha x k i j := by
  -- the readE slot at `k i j` IS `activeSlotE M (tach M) ha k i j` (definitionally).
  have hslot : readE M (tach M) ha
        (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x) k i j
      = pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x
          (activeSlotE M (tach M) ha k i j) := rfl
  have hslot' : readE M (tach M) ha x k i j = x (activeSlotE M (tach M) ha k i j) := rfl
  rw [hslot, hslot']
  have hne : activeSlotE M (tach M) ha k i j ≠ leafPivot M ha hL h0r h0c := by
    rw [← leafSlot_zero_eq_leafPivotGen M ha hL h0r h0c]
    intro h
    rw [activeSlotE, leafSlot] at h
    have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective h
    rw [Sigma.mk.inj_iff] at h2
    have hkval : k.val = L - 1 := congrArg Fin.val h2.1
    exact hk hkval
  unfold pivotBlowupOn
  rw [if_neg hne, if_pos (activeSlotE_mem_activeMGen M ha k hk i j)]

/-! ## The general-`L` LIVE-leaf ∘ kLDU interior chart -/

/-- **The general-`L` LIVE-leaf ∘ kLDU interior achiever chart** `phiFlatLiveAt M ha hL leafPivot
(kLDU x)` — the injective live-leaf chart (`RouteMLeafChart.phiFlatLiveAt`) with the K-slots
LDU-straightened (`RouteMKLens.kLDU`) so the per-boundary frame det is a monomial. The general-`L`
lift of `RouteMInteriorLiveContract.interiorLivePhi`. -/
noncomputable def interiorLivePhiGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) :=
  fun x => phiFlatLiveAt M ha hL (leafPivot M ha hL h0r h0c) (kLDU M (tach M) ha x)

/-- **The general-`L` LIVE-leaf ∘ kLDU unit factor** — the radial quotient
`routeMCore(φ x)/(x leafPivot)²`. The general-`L` lift of `interiorLiveUnit`. -/
noncomputable def interiorLiveUnitGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    (Fin (routeMAmbient M) → ℝ) → ℝ :=
  fun x => VvalGen (x (leafPivot M ha hL h0r h0c)) M (tach M)
    (genBlkFlatLive M (tach M) ha
      (rfinFixedPivot M ha hL (kLDU M (tach M) ha x)) (kLDU M (tach M) ha x))
    (hleStruct M (tach M) ha)

/-- **`(kLDU x) leafPivot = x leafPivot`** at general `L` — the radial axis survives `kLDU` (a leaf
slot, not a K-slot; `kLDU` is identity off K-slots). The leaf pivot `leafPivot = leafSlot (L−1) 0 0`
decodes via `chartIdxEquiv` to the Schur slot at boundary `L−1`; the kLDU K-arm at boundary `k = L−1`
reads the K-core `readK x (L−1) : Matrix (Fin (Text(L+1))) …` which is `0×0` (`Text(L+1) = 0`), so the
K-arm is vacuous and the leaf slot falls through `kLDU`'s identity branch. The general-`L` lift of
`RouteMInteriorLiveContract.kLDU_leafPivot`. -/
theorem kLDU_leafPivotGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ) :
    (kLDU M (tach M) ha x) (leafPivot M ha hL h0r h0c) = x (leafPivot M ha hL h0r h0c) := by
  rw [kLDU, leafPivot, leafSlot]
  simp only [Equiv.apply_symm_apply]
  have hTL1 : Text M (tach M) (L + 1) = 0 := Text_Lsucc_eq_zero M hL
  split
  · -- K-arm: `qK : Fin (Text(k+2) · Text(k+2)) = Fin 0` is uninhabited (the leaf K-block is `0×0`).
    rename_i qK _
    have hz : Text M (tach M) ((⟨L - 1, by omega⟩ : Fin L).val + 1 + 1)
          * Text M (tach M) ((⟨L - 1, by omega⟩ : Fin L).val + 1 + 1) = 0 := by
      change Text M (tach M) (L - 1 + 1 + 1) * Text M (tach M) (L - 1 + 1 + 1) = 0
      rw [show L - 1 + 1 + 1 = L + 1 by omega, hTL1, Nat.mul_zero]
    exact (Fin.cast hz qK).elim0
  · rfl

/-- **The rate of the general-`L` LIVE-leaf ∘ kLDU chart** (banked, NO bridge): `routeMCore M (φ x) =
(x leafPivot)² · interiorLiveUnitGen x`. The radial axis survives `kLDU` (`kLDU_leafPivotGen`), so
`phiFlatLiveAt_rate` at the point `kLDU x` transfers verbatim. The general-`L` lift of
`routeMCore_interiorLivePhi`. -/
theorem routeMCore_interiorLivePhiGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (interiorLivePhiGen M ha hL h0r h0c x)
      = (x (leafPivot M ha hL h0r h0c)) ^ 2 * interiorLiveUnitGen M ha hL h0r h0c x := by
  rw [interiorLivePhiGen, phiFlatLiveAt_rate M ha hL
    (leafPivot M ha hL h0r h0c) (kLDU M (tach M) ha x), kLDU_leafPivotGen M ha hL h0r h0c x]
  rfl

/-- `0 ≤ interiorLiveUnitGen` (sum of squares, banked `VvalGen_nonneg`). -/
theorem interiorLiveUnitGen_nonneg (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ) :
    0 ≤ interiorLiveUnitGen M ha hL h0r h0c x :=
  VvalGen_nonneg _ M (tach M) _ _

/-! ## The kLDU / pivotBlowupOn commute (the load-bearing map identity) -/

/-- **`kLDU` is identity on every `activeMGen` slot** at general `L` — the E-block slots decode to
`frameSplitEquiv`'s `Sum.inr` (E-role, kLDU identity arm); the leaf slots sit at the leaf boundary
`L−1` where the K-block is `0×0` (`Text(L+1) = 0`), so they fall through the identity arm too. The
shared atom for the commute; the general-`L` lift of `RouteMInteriorLiveContract.kLDU_eq_on_activeM`. -/
theorem kLDU_eq_on_activeMGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (x : Fin (routeMAmbient M) → ℝ) {q : Fin (routeMAmbient M)} (hq : q ∈ activeMGen M ha) :
    (kLDU M (tach M) ha x) q = x q := by
  rw [activeMGen, Finset.mem_biUnion] at hq
  obtain ⟨k', _, hk'⟩ := hq
  by_cases hk'L : k'.val = L - 1
  · -- leaf slot at boundary `L − 1`.
    rw [activeImgGen, dif_pos hk'L, Finset.mem_image] at hk'
    obtain ⟨p, _, hp⟩ := hk'; subst hp
    rw [kLDU, leafSlot]; simp only [Equiv.apply_symm_apply]
    have hTL1 : Text M (tach M) (L + 1) = 0 := Text_Lsucc_eq_zero M ha.hL
    split
    · rename_i qK _
      exact (Fin.cast (by
        change Text M (tach M) (L - 1 + 1 + 1) * Text M (tach M) (L - 1 + 1 + 1) = 0
        rw [show L - 1 + 1 + 1 = L + 1 by omega, hTL1, Nat.mul_zero]) qK).elim0
    · rfl
  · -- E-block slot at an interior boundary `k' ≠ L − 1`.
    rw [activeImgGen, dif_neg hk'L, Finset.mem_image] at hk'
    obtain ⟨p, _, hp⟩ := hk'; subst hp
    rw [kLDU, activeSlotE]; simp only [Equiv.apply_symm_apply]

/-- **The kLDU / pivotBlowupOn commute at general `L`** — `pivotBlowupOn activeMGen leafPivot (kLDU x)
= kLDU (pivotBlowupOn activeMGen leafPivot x)`. `activeMGen = {E-block ∪ leaf slots}` (NO K-slots),
`kLDU` touches ONLY K-slots, so the two maps act on disjoint coordinate sets. The funext casework: a
K-branch `q` lands in the kLDU K-arm on both sides (`kLens(readK · k)`, equal by `readK_pbo_allGen`), and
`pbo` fixes it (K ∉ activeMGen); a non-K `q` lands in the kLDU identity arm, where `pbo` and `kLDU`
commute because the pivot + activeMGen slots `pbo` scales are all kLDU-fixed (`kLDU_eq_on_activeMGen`).
The general-`L` lift of `RouteMInteriorLiveContract.interiorLive_commute`. -/
theorem interiorLive_commuteGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ) :
    pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) (kLDU M (tach M) ha x)
      = kLDU M (tach M) ha
        (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x) := by
  set p₀ := leafPivot M ha hL h0r h0c with hp₀
  funext q
  by_cases hpiv : q = p₀
  · subst hpiv
    rw [pivotBlowupOn, if_pos rfl, kLDU_leafPivotGen M ha hL h0r h0c x,
        kLDU_leafPivotGen M ha hL h0r h0c (pivotBlowupOn (activeMGen M ha) p₀ x),
        pivotBlowupOn, if_pos rfl]
  · by_cases hact : q ∈ activeMGen M ha
    · rw [pivotBlowupOn, if_neg hpiv, if_pos hact,
          kLDU_eq_on_activeMGen M ha x hact, kLDU_leafPivotGen M ha hL h0r h0c x,
          kLDU_eq_on_activeMGen M ha (pivotBlowupOn (activeMGen M ha) p₀ x) hact,
          pivotBlowupOn, if_neg hpiv, if_pos hact]
    · -- spectator: both kLDU calls land in the same arm; K-arm equal by `readK_pbo_allGen`, identity
      -- arm by `pbo` fixing the slot (`q ∉ activeMGen`, `q ≠ p₀`).
      rw [pivotBlowupOn, if_neg hpiv, if_neg hact, kLDU, kLDU]
      have hpboq : pivotBlowupOn (activeMGen M ha) p₀ x q = x q := by
        rw [pivotBlowupOn, if_neg hpiv, if_neg hact]
      match hc : chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL q with
      | ⟨k, Sum.inl s⟩ =>
        have hmat : readK M (tach M) ha (pivotBlowupOn (activeMGen M ha) p₀ x) k
            = readK M (tach M) ha x k := by
          funext a b; exact readK_pbo_allGen M ha hL h0r h0c x k a b
        simp only [hmat, hpboq]
      | ⟨k, Sum.inr s⟩ => simp only [hpboq]

/-! ## H2 — the multi-axis Jacobian exponent vector `leafHGen` -/

/-- **The `ChartIdx`-indexed K-diagonal exponent placement at general `L`** (the general-`L` lift of
`RouteMInteriorLiveContract.liveLeafHOnIdx`). At a frame slot (`Sum.inl s`), boundary `k`, the K-role
branch decodes `(i,j) = finProdFinEquiv.symm qK`; on the diagonal `i = j` it returns the per-pivot
exponent `(r_k + c_k) + 2·(t_k − 1 − i)` (the Schur frame `r_k+c_k` + the LDU core `2(t_k−1−i)`), `0`
off-diagonal / X,N,E / lift. The L=2 `liveLeafHOnIdx` already matched on arbitrary `k` (only its
consumers were `Fin 2`-pinned) — this restates it at general `L`. -/
noncomputable def liveLeafHOnIdxGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    ChartIdx M (tDesc M (tach M)) → ℕ := fun q =>
  match q with
  | ⟨k, Sum.inl s⟩ =>
    match frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s with
    | Sum.inl (Sum.inl (Sum.inl qK)) =>
      let ij := finProdFinEquiv.symm qK
      if ij.1 = ij.2 then
        (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
          + (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
          + 2 * (Text M (tach M) (k.val + 2) - 1 - ij.1.val)
      else 0
    | _ => 0
  | ⟨_, Sum.inr _⟩ => 0

/-- **H2 — the multi-axis Jacobian exponent vector at general `L`** for the LIVE-leaf ∘ kLDU chart. The
binding axis `leafPivot` carries `minAdm−1` (override); the lensed K-diagonal axes at EVERY interior
boundary carry the frame+LDU exponents `liveLeafHOnIdxGen`; `0` elsewhere. At `leafPivot` the placement
is `0` (the leaf boundary's K-block is empty, `Text(L+1) = 0`), so the override introduces the genuine
radial exponent without masking a K exponent. The general-`L` lift of
`RouteMInteriorLiveContract.interiorLive_leafH`. -/
noncomputable def interiorLive_leafHGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) : Fin (routeMAmbient M) → ℕ := fun j =>
  if j = leafPivot M ha hL h0r h0c then
    minAdm M - 1
  else
    liveLeafHOnIdxGen M ha (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL j)

/-- **H2 — the binding axis carries `minAdm−1`** (the pivot override is `if_pos rfl`). The general-`L`
lift of `interiorLive_leafH_pivot`. -/
theorem interiorLive_leafHGen_pivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    interiorLive_leafHGen M ha hL h0r h0c (leafPivot M ha hL h0r h0c) = minAdm M - 1 := by
  rw [interiorLive_leafHGen, if_pos rfl]

end DLNFibre.DLN.RLCT
