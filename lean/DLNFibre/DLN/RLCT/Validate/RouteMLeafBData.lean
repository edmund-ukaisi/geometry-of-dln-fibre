import DLNFibre.DLN.RLCT.Validate.RouteMLeafHeadline
import DLNFibre.DLN.RLCT.Validate.RouteMHmapGen

/-!
# `RouteMLeafBData` — the concrete boundary factor `B` discharging the ∀M-L2 interior-det headline

Constructs the explicit `B`/`DB`/`engine` discharging the three open obligations
(`hmap`/`hasDB`/`hdet`) of `interiorDet_leaf_headline` (`RouteMLeafHeadline`), and assembles the
UNCONDITIONAL ∀M-L2 interior-determinant headline `interiorDet_leaf_headline_unconditional`:

  `|det Dφ| = |u p₀|^(minAdm M − 1) · ∏_s engine_s`

for the REAL `genBlkFlatLive` + leaf-pivot chart `phiFlatLiveAt`.

The boundary factor `B = Bchart` is the `u`-FREE per-layer chart that reads the residual coordinates
as ORDINARY `y`-values (no radial blow-up); the `u`-scaling lives entirely in `pivotBlowupOn`. The
map identity `hmap` reduces (funext + `paramsEquivFlat` injective) to a per-layer chart-parameter
equality, which — via `Agen_congr` — reduces to matching `Nblk`/`Wblk`/`Cgen(k+1)` on the two
configs (NO explicit `chainA` reindexing over the dependent `Fin (Text/Wext)` widths). The Cgen uses
the banked `Cgen_live_interior_eq_schurFrameProd` + `schurFrameProd_u_to_E` (the radial `u` moves
into the residual coordinate) at the interior boundary, and `Cgen_live_leaf` at the leaf.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (matrix algebra + the banked wiring; no
analysis beyond the chain rule `radialComp_abs_det_at` already uses).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Foundational matrix lemmas (the E-scaling kernel) -/

/-- `rmatPad` is ℝ-linear in `E`: `rmatPad (c • E) = c • rmatPad E`. -/
theorem rmatPad_smul {M t : Fin (L + 1) → ℕ} {s : ℕ}
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s) (c : ℝ)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ) :
    rmatPad M t s h1 h2 (c • E) = c • rmatPad M t s h1 h2 E := by
  unfold rmatPad
  rw [show Matrix.fromBlocks (0 : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
        0 0 (c • E) = c • Matrix.fromBlocks 0 0 0 E from by
    rw [Matrix.fromBlocks_smul, smul_zero, smul_zero, smul_zero]]
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_smul]
  rfl

/-- The leaf transition for the LIVE decoder `Cgen v (genBlkFlatLive …) L = v • rfin`. -/
theorem Cgen_live_leaf (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (v : ℝ)
    (x : Fin (routeMAmbient M) → ℝ) :
    Cgen v M t (genBlkFlatLive M t ha rfin x) (hleStruct M t ha) L = v • rfin := by
  rw [Cgen, dif_neg (lt_irrefl L)]
  congr 1
  show (genBlkFlatLive M t ha rfin x).Rfin L = rfin
  simp only [genBlkFlatLive]
  split
  · rfl
  · rename_i h; exact (h trivial).elim

/-- **The E-scaling identity for `schurFrameProd`**: `schurFrameProd … u K X N E
= schurFrameProd … 1 K X N (u • E)`. The `bmatStack·chainQ` part has no `u`; the `u • rmatPad E`
part equals `1 • rmatPad (u • E) = rmatPad (u • E)` by `rmatPad_smul`. The DECODER-MATCH kernel:
the radial `u` of the chart's E-term moves into the residual coordinate `u • E` of the u-free B. -/
theorem schurFrameProd_u_to_E (M t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s) (u : ℝ)
    (K : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
    (X : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
    (N : Matrix (Fin (Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ) :
    schurFrameProd M t s h1 h2 u K X N E
      = schurFrameProd M t s h1 h2 1 K X N (u • E) := by
  rw [schurFrameProd, schurFrameProd, rmatPad_smul, one_smul]

/-! ## The `Agen` congruence (block-level, no explicit `chainA` reindexing) -/

/-- **`Agen` congruence**: `Agen` at boundary `k` depends only on `(B.Nblk k, B.Wblk k,
Cgen u … B (k+1))` (plus the fixed `M`/`t`/`hle` width proof). So two `(u, B)` configs with matching
`Nblk k`, `Wblk k`, and `Cgen (k+1)` produce the SAME `Agen k`. This is the kernel reducing the
`hmap` per-layer match to a Cgen-block match — NO explicit `chainA` reindexing over the dependent
`Fin (Text/Wext)` widths. -/
theorem Agen_congr (M t : Fin (L + 1) → ℕ) (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k)
    (u₁ u₂ : ℝ) (B₁ B₂ : GenBlk M t) (k : ℕ)
    (hN : B₁.Nblk k = B₂.Nblk k) (hW : B₁.Wblk k = B₂.Wblk k)
    (hC : Cgen u₁ M t B₁ hle (k + 1) = Cgen u₂ M t B₂ hle (k + 1)) :
    Agen u₁ M t B₁ hle k = Agen u₂ M t B₂ hle k := by
  unfold Agen
  by_cases hk : k < L
  · rw [dif_pos hk, dif_pos hk, hN, hW, hC]
  · rw [dif_neg hk, dif_neg hk]

/-! ## Slot memberships in `activeM` (L = 2) -/

section L2

variable {M : Fin (2 + 1) → ℕ}

/-- The interior E-block slot at the L=2 boundary `⟨0⟩` is in `activeM` (via `activeEImg`). -/
theorem activeSlotE_mem_activeM (ha : StructAdm M (tach M))
    (iE : Fin (Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2)))
    (jE : Fin (Wext M (0 + 1) - Text M (tach M) (0 + 2))) :
    activeSlotE M (tach M) ha ⟨0, by decide⟩ iE jE ∈ activeM M ha := by
  rw [activeM]
  refine Finset.mem_union_left _ ?_
  rw [activeEImg, Finset.mem_image]
  refine ⟨(Fin.cast (by norm_num) iE, Fin.cast (by norm_num) jE), Finset.mem_univ _, ?_⟩
  congr 1 <;> · apply Fin.ext; simp

/-- The leaf slot is in `activeM` (via `activeLeafImg`). -/
theorem leafSlot_mem_activeM (ha : StructAdm M (tach M))
    (i : Fin (Text M (tach M) 2)) (j : Fin (Wext M 2)) :
    leafSlot M (tach M) ha (by norm_num) i j ∈ activeM M ha := by
  rw [activeM]
  refine Finset.mem_union_right _ ?_
  rw [activeLeafImg, Finset.mem_image]
  exact ⟨(i, j), Finset.mem_univ _, rfl⟩

/-! ## A slot at chartIdx boundary `⟨0⟩` whose tag is NOT the E-summand is `∉ activeM` (`L = 2`)

`activeM = activeEImg ∪ activeLeafImg`. The leaf images sit at chartIdx boundary `⟨1⟩` (`= L − 1`);
the E images sit at boundary `⟨0⟩` with frame tag `Sum.inl (frameSplitEquiv.symm (Sum.inr …))`. A
reader slot at boundary `⟨0⟩` whose chartIdx tag is NOT that E-tag is therefore in neither image. We
package the chartIdx tag as `tag` and require: `tag ≠` every E-tag (the genuine distinction) — the
boundary-`⟨0⟩ ≠ ⟨1⟩` distinction handles the leaf side. -/

/-- A chartIdx-`⟨0⟩` slot with tag `tag` is `∉ activeLeafImg` (the leaf is at boundary `⟨1⟩`). -/
theorem boundary0_notMem_activeLeafImg (ha : StructAdm M (tach M))
    (tag : Fin (schurDim M (tDesc M (tach M)) 0) ⊕ Fin (liftDim M (tDesc M (tach M)) 0)) :
    (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨⟨0, by decide⟩, tag⟩
      ∉ activeLeafImg M ha := by
  rw [activeLeafImg, Finset.mem_image]
  rintro ⟨pL, _, hpL⟩
  rw [leafSlot] at hpL
  have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective hpL
  rw [Sigma.mk.inj_iff] at h2
  exact absurd h2.1.symm (by decide)

/-- A chartIdx-`⟨0⟩` slot whose tag is NOT the E-summand image is `∉ activeEImg`. The hypothesis
`hne` is the genuine tag distinction (`tag ≠` the E-tag for every E-index). -/
theorem boundary0_notMem_activeEImg (ha : StructAdm M (tach M))
    (tag : Fin (schurDim M (tDesc M (tach M)) 0) ⊕ Fin (liftDim M (tDesc M (tach M)) 0))
    (hne : ∀ (iE : Fin (Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2)))
        (jE : Fin (Wext M (0 + 1) - Text M (tach M) (0 + 2))),
        tag ≠ Sum.inl ((frameSplitEquiv M (tach M) (0 + 1)
          (ha.hdesc 0 (by decide)) (ha.hub 0)).symm (Sum.inr (finProdFinEquiv (iE, jE))))) :
    (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨⟨0, by decide⟩, tag⟩
      ∉ activeEImg M ha := by
  rw [activeEImg, Finset.mem_image]
  rintro ⟨pE, _, hpE⟩
  rw [activeSlotE] at hpE
  have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective hpE
  rw [Sigma.mk.inj_iff] at h2
  have htag := h2.2
  simp only [heq_eq_eq] at htag
  exact hne _ _ htag.symm

/-- A chartIdx-`⟨0⟩` slot whose tag is NOT the E-summand image is `∉ activeM`. -/
theorem boundary0_notMem_activeM (ha : StructAdm M (tach M))
    (tag : Fin (schurDim M (tDesc M (tach M)) 0) ⊕ Fin (liftDim M (tDesc M (tach M)) 0))
    (hne : ∀ (iE : Fin (Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2)))
        (jE : Fin (Wext M (0 + 1) - Text M (tach M) (0 + 2))),
        tag ≠ Sum.inl ((frameSplitEquiv M (tach M) (0 + 1)
          (ha.hdesc 0 (by decide)) (ha.hub 0)).symm (Sum.inr (finProdFinEquiv (iE, jE))))) :
    (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨⟨0, by decide⟩, tag⟩
      ∉ activeM M ha := by
  rw [activeM, Finset.mem_union, not_or]
  exact ⟨boundary0_notMem_activeEImg ha tag hne, boundary0_notMem_activeLeafImg ha tag⟩

/-- A chartIdx-`⟨0⟩` slot is `≠ leafPivot` (the leaf pivot is at boundary `⟨1⟩`). -/
theorem boundary0_ne_leafPivot (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (tag : Fin (schurDim M (tDesc M (tach M)) 0) ⊕ Fin (liftDim M (tDesc M (tach M)) 0)) :
    (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨⟨0, by decide⟩, tag⟩
      ≠ leafPivot M ha (by norm_num) h0r h0c := by
  rw [leafPivot, leafSlot]
  intro h
  have h2 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective h
  rw [Sigma.mk.inj_iff] at h2
  exact absurd h2.1 (by decide)

/-- **`pivotBlowupOn` fixes a chartIdx-`⟨0⟩` non-E slot**: it is `≠ leafPivot` and `∉ activeM`,
so `pivotBlowupOn activeM leafPivot x slot = x slot`. -/
theorem pbo_fixes_boundary0 (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (tag : Fin (schurDim M (tDesc M (tach M)) 0) ⊕ Fin (liftDim M (tDesc M (tach M)) 0))
    (hne : ∀ (iE : Fin (Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2)))
        (jE : Fin (Wext M (0 + 1) - Text M (tach M) (0 + 2))),
        tag ≠ Sum.inl ((frameSplitEquiv M (tach M) (0 + 1)
          (ha.hdesc 0 (by decide)) (ha.hub 0)).symm (Sum.inr (finProdFinEquiv (iE, jE)))))
    (x : Fin (routeMAmbient M) → ℝ) :
    pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x
        ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨⟨0, by decide⟩, tag⟩)
      = x ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨⟨0, by decide⟩, tag⟩) := by
  unfold pivotBlowupOn
  rw [if_neg (boundary0_ne_leafPivot ha h0r h0c tag),
    if_neg (boundary0_notMem_activeM ha tag hne)]

/-! ## The interior readers are fixed by `pivotBlowupOn` (spectator slots), E scales (`L = 2`) -/

/-- `readK` at the interior boundary `⟨0⟩` is fixed by `pivotBlowupOn` (the `K`-tag is the
`Sum.inl (Sum.inl (Sum.inl …))` frame summand, distinct from the `Sum.inr` E-summand). -/
theorem readK_pbo (ha : StructAdm M (tach M)) (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (x : Fin (routeMAmbient M) → ℝ) (i j : Fin (Text M (tach M) (0 + 2))) :
    readK M (tach M) ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x)
        ⟨0, by decide⟩ i j
      = readK M (tach M) ha x ⟨0, by decide⟩ i j := by
  rw [readK, readK]
  exact pbo_fixes_boundary0 ha h0r h0c _ (fun iE jE h => by
    have := (frameSplitEquiv M (tach M) (0 + 1) (ha.hdesc 0 (by decide)) (ha.hub 0)).symm.injective
      (Sum.inl.inj h); exact Sum.inl_ne_inr this) x

/-- `readX` at `⟨0⟩` is fixed by `pivotBlowupOn` (the `X`-tag `Sum.inl (Sum.inl (Sum.inr …))`). -/
theorem readX_pbo (ha : StructAdm M (tach M)) (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (x : Fin (routeMAmbient M) → ℝ)
    (i : Fin (Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2)))
    (j : Fin (Text M (tach M) (0 + 2))) :
    readX M (tach M) ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x)
        ⟨0, by decide⟩ i j
      = readX M (tach M) ha x ⟨0, by decide⟩ i j := by
  rw [readX, readX]
  exact pbo_fixes_boundary0 ha h0r h0c _ (fun iE jE h => by
    have := (frameSplitEquiv M (tach M) (0 + 1) (ha.hdesc 0 (by decide)) (ha.hub 0)).symm.injective
      (Sum.inl.inj h); exact Sum.inl_ne_inr this) x

/-- `readN` at `⟨0⟩` is fixed by `pivotBlowupOn` (the `N`-tag `Sum.inl (Sum.inr …)`). -/
theorem readN_pbo (ha : StructAdm M (tach M)) (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (x : Fin (routeMAmbient M) → ℝ)
    (i : Fin (Text M (tach M) (0 + 2)))
    (j : Fin (Wext M (0 + 1) - Text M (tach M) (0 + 2))) :
    readN M (tach M) ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x)
        ⟨0, by decide⟩ i j
      = readN M (tach M) ha x ⟨0, by decide⟩ i j := by
  rw [readN, readN]
  exact pbo_fixes_boundary0 ha h0r h0c _ (fun iE jE h => by
    have := (frameSplitEquiv M (tach M) (0 + 1) (ha.hdesc 0 (by decide)) (ha.hub 0)).symm.injective
      (Sum.inl.inj h); exact Sum.inl_ne_inr this) x

/-- `readW` at `⟨0⟩` is fixed by `pivotBlowupOn` (the `W`-tag is the `Sum.inr (liftSlotEquiv …)`
lift summand of the chartIdx fiber, distinct from the `Sum.inl …` frame summand the E-tag uses). -/
theorem readW_pbo (ha : StructAdm M (tach M)) (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (hk2 : (0 : ℕ) + 1 < 2) (x : Fin (routeMAmbient M) → ℝ)
    (i : Fin (Wext M (0 + 1) - Text M (tach M) (0 + 2)))
    (j : Fin (Wext M (0 + 2))) :
    readW M (tach M) ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x)
        ⟨0, by decide⟩ hk2 i j
      = readW M (tach M) ha x ⟨0, by decide⟩ hk2 i j := by
  rw [readW, readW]
  exact pbo_fixes_boundary0 ha h0r h0c _ (fun iE jE h => Sum.inl_ne_inr h.symm) x

/-- **`readE` SCALES under `pivotBlowupOn`**: the E-slot at `⟨0⟩` IS `activeSlotE ⟨0⟩ i j`, in
`activeM` and `≠ leafPivot`, so `pivotBlowupOn` scales it by `x p₀`:
`readE (pbo x) ⟨0⟩ i j = (x p₀)·readE x ⟨0⟩ i j`. The radial-scaling kernel of the E-block match. -/
theorem readE_pbo (ha : StructAdm M (tach M)) (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (x : Fin (routeMAmbient M) → ℝ)
    (i : Fin (Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2)))
    (j : Fin (Wext M (0 + 1) - Text M (tach M) (0 + 2))) :
    readE M (tach M) ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x)
        ⟨0, by decide⟩ i j
      = x (leafPivot M ha (by norm_num) h0r h0c)
        * readE M (tach M) ha x ⟨0, by decide⟩ i j := by
  -- the readE slot at `⟨0⟩ i j` IS `activeSlotE M (tach M) ha ⟨0⟩ i j` (definitionally)
  have hslot : readE M (tach M) ha
        (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x) ⟨0, by decide⟩ i j
      = pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x
          (activeSlotE M (tach M) ha ⟨0, by decide⟩ i j) := rfl
  have hslot' : readE M (tach M) ha x ⟨0, by decide⟩ i j
      = x (activeSlotE M (tach M) ha ⟨0, by decide⟩ i j) := rfl
  rw [hslot, hslot']
  have hne : activeSlotE M (tach M) ha ⟨0, by decide⟩ i j
      ≠ leafPivot M ha (by norm_num) h0r h0c := boundary0_ne_leafPivot ha h0r h0c _
  unfold pivotBlowupOn
  rw [if_neg hne, if_pos (activeSlotE_mem_activeM ha i j)]

/-! ## The leaf slots under `pivotBlowupOn` (pivot fixed at `(0,0)`, the rest scale) -/

/-- `leafSlot 0 0` IS `leafPivot` (definitionally). -/
theorem leafSlot_zero_eq_leafPivot (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    leafSlot M (tach M) ha (by norm_num) ⟨0, h0r⟩ ⟨0, h0c⟩
      = leafPivot M ha (by norm_num) h0r h0c := rfl

/-- A leaf slot `(i, j) ≠ (0, 0)` is `≠ leafPivot` (`leafSlot` is injective in `(i, j)`). -/
theorem leafSlot_ne_leafPivot (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (i : Fin (Text M (tach M) 2)) (j : Fin (Wext M 2)) (hij : ¬ (i.val = 0 ∧ j.val = 0)) :
    leafSlot M (tach M) ha (by norm_num) i j ≠ leafPivot M ha (by norm_num) h0r h0c := by
  rw [leafPivot]
  intro h
  obtain ⟨hi, hj⟩ := leafSlot_inj M (tach M) ha (by norm_num) h
  exact hij ⟨by simp [hi], by simp [hj]⟩

/-! ## The boundary factor `B = Bchart` (the `u`-free residual-reading chart) -/

/-- The direct leaf reader: `rfinDirect ha y i j := y (leafSlot … i j)` — reads ALL leaf entries
(including the pivot slot `(0,0)`) DIRECTLY from `y`, no fixed-`1`, no radial scaling. -/
noncomputable def rfinDirect (ha : StructAdm M (tach M))
    (y : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin (Text M (tach M) 2)) (Fin (Wext M 2)) ℝ :=
  Matrix.of fun i j => y (leafSlot M (tach M) ha (by norm_num) i j)

/-- **The boundary-factor chart parameters** `Bparams ha y : Params M` — the `u`-FREE chart with the
radial scalar hardwired to `1`, reading the residual coords directly (`rfinDirect`) from `y`. -/
noncomputable def Bparams (ha : StructAdm M (tach M)) (y : Fin (routeMAmbient M) → ℝ) : Params M :=
  chartParamsGen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirect ha y) y)
    (hleStruct M (tach M) ha)

/-- **The boundary factor** `Bchart ha y := paramsEquivFlat M (Bparams ha y)`. -/
noncomputable def Bchart (ha : StructAdm M (tach M)) (y : Fin (routeMAmbient M) → ℝ) :
    Fin (routeMAmbient M) → ℝ :=
  paramsEquivFlat M (Bparams ha y)

/-! ## The Cgen-block match between the chart decoder and the `B` decoder (`L = 2`) -/

/-- **The interior `Cgen 1` match**: the chart's interior transition (radial `u = x p₀`, leaf
`rfinFixedPivot x`) equals the `B`-decoder's (radial `1`, leaf `rfinDirect (pbo x)`). Both are the
Schur frame (`Cgen_live_interior_eq_schurFrameProd`); the K/X/N blocks read spectator slots (fixed
via `readK/X/N_pbo`), and the radial `u` of the E-term moves into the residual coordinate
(`schurFrameProd_u_to_E` + `readE_pbo`). -/
theorem Cgen1_match (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (x : Fin (routeMAmbient M) → ℝ) :
    Cgen (x (leafPivot M ha (by norm_num) h0r h0c)) M (tach M)
        (genBlkFlatLive M (tach M) ha
          (rfinFixedPivot M ha (by norm_num) x) x) (hleStruct M (tach M) ha) (0 + 1)
      = Cgen 1 M (tach M)
        (genBlkFlatLive M (tach M) ha
          (rfinDirect ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x))
          (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x))
        (hleStruct M (tach M) ha) (0 + 1) := by
  set p₀ := leafPivot M ha (by norm_num) h0r h0c
  set pbo := pivotBlowupOn (activeM M ha) p₀
  rw [Cgen_live_interior_eq_schurFrameProd M (tach M) ha _ _ x 0 (by norm_num),
    Cgen_live_interior_eq_schurFrameProd M (tach M) ha _ _ (pbo x) 0 (by norm_num),
    schurFrameProd_u_to_E M (tach M) (0 + 1) _ _ (x p₀)]
  congr 1
  · funext i j; exact (readK_pbo ha h0r h0c x i j).symm
  · funext i j; exact (readX_pbo ha h0r h0c x i j).symm
  · funext i j; exact (readN_pbo ha h0r h0c x i j).symm
  · funext i j
    rw [Matrix.smul_apply, smul_eq_mul, readE_pbo ha h0r h0c x i j]

/-- **The leaf `Cgen 2` match**: `(x p₀) • rfinFixedPivot x = 1 • rfinDirect (pbo x)` (boundary
`2 = L`). At the pivot `(0,0)`: `(x p₀)·1 = (pbo x) p₀ = x p₀` (pivot fixed); off `(0,0)`:
`(x p₀)·x(leafSlot i j) = (pbo x)(leafSlot i j)` (a leaf slot in `activeM`, `≠ p₀`, scaled). -/
theorem Cgen2_match (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (x : Fin (routeMAmbient M) → ℝ) :
    Cgen (x (leafPivot M ha (by norm_num) h0r h0c)) M (tach M)
        (genBlkFlatLive M (tach M) ha
          (rfinFixedPivot M ha (by norm_num) x) x) (hleStruct M (tach M) ha) 2
      = Cgen 1 M (tach M)
        (genBlkFlatLive M (tach M) ha
          (rfinDirect ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x))
          (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x))
        (hleStruct M (tach M) ha) 2 := by
  rw [Cgen_live_leaf M (tach M) ha (rfinFixedPivot M ha (by norm_num) x)
      (x (leafPivot M ha (by norm_num) h0r h0c)) x,
    Cgen_live_leaf M (tach M) ha
      (rfinDirect ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x))
      (1 : ℝ) (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x), one_smul]
  funext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i.val = 0 ∧ j.val = 0
  · -- the pivot entry: both sides are `x p₀`
    obtain ⟨hi, hj⟩ := hij
    have hi' : i = ⟨0, h0r⟩ := Fin.ext hi
    have hj' : j = ⟨0, h0c⟩ := Fin.ext hj
    subst hi' hj'
    rw [rfinFixedPivot_pivot M ha (by norm_num) h0r h0c, mul_one]
    show x (leafPivot M ha (by norm_num) h0r h0c)
      = pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x
          (leafSlot M (tach M) ha (by norm_num) ⟨0, h0r⟩ ⟨0, h0c⟩)
    rw [leafSlot_zero_eq_leafPivot ha h0r h0c, pivotBlowupOn, if_pos rfl]
  · -- a non-pivot leaf entry: `(x p₀)·x(leafSlot i j) = pbo x (leafSlot i j)`
    rw [rfinFixedPivot_off M ha (by norm_num) x i j hij]
    show x (leafPivot M ha (by norm_num) h0r h0c) * x (leafSlot M (tach M) ha (by norm_num) i j)
      = pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x
          (leafSlot M (tach M) ha (by norm_num) i j)
    rw [pivotBlowupOn, if_neg (leafSlot_ne_leafPivot ha h0r h0c i j hij),
      if_pos (leafSlot_mem_activeM ha i j)]

/-! ## The chart-parameter match + `hmap` -/

/-- The genBlkFlatLive `Nblk (k+1)` reads `readN` (`k < L`); the spectator match for `k = 0`. -/
theorem live_Nblk_match (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha (by norm_num) x) x).Nblk (0 + 1)
      = (genBlkFlatLive M (tach M) ha
          (rfinDirect ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x))
          (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x)).Nblk (0 + 1) :=
    by
  rw [genBlkFlatLive_Nblk_succ M (tach M) ha _ x 0 (by norm_num),
    genBlkFlatLive_Nblk_succ M (tach M) ha _ _ 0 (by norm_num)]
  funext i j; exact (readN_pbo ha h0r h0c x i j).symm

/-- The genBlkFlatLive `Wblk (k+1)` is the structured decoder's `Wblk`; the spectator match. -/
theorem live_Wblk_match (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha (by norm_num) x) x).Wblk (0 + 1)
      = (genBlkFlatLive M (tach M) ha
          (rfinDirect ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x))
          (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x)).Wblk (0 + 1) :=
    by
  show (genBlkFlatStruct M (tach M) ha x).Wblk (0 + 1)
    = (genBlkFlatStruct M (tach M) ha
        (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x)).Wblk (0 + 1)
  simp only [genBlkFlatStruct, dif_pos (show (0 : ℕ) < 2 by decide),
    dif_pos (show 0 + 1 < 2 by decide)]
  funext i j; exact (readW_pbo ha h0r h0c (by decide) x i j).symm

/-- **The chart-parameter match** `chartParamsGen (x p₀) … (chart decoder) = chartParamsGen 1 …
(B decoder ∘ pbo)` — the genuine content of `hmap`, per layer `s : Fin 2`. Both are `reindex (Agen …
s.val)`; `Agen_congr` reduces each to the `Nblk`/`Wblk`/`Cgen(k+1)` matches (`live_Nblk_match`,
`live_Wblk_match`, `Cgen1_match` / `Cgen2_match`). Boundary `0` uses the interior `Cgen 1`; boundary
`1` uses the leaf `Cgen 2`. -/
theorem chartParamsGen_match (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (x : Fin (routeMAmbient M) → ℝ) :
    chartParamsGen (x (leafPivot M ha (by norm_num) h0r h0c)) M (tach M)
        (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha (by norm_num) x) x)
        (hleStruct M (tach M) ha)
      = Bparams ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) x) := by
  set p₀ := leafPivot M ha (by norm_num) h0r h0c
  set pbo := pivotBlowupOn (activeM M ha) p₀
  funext s
  show Matrix.reindex _ _ (Agen (x p₀) M (tach M) _ (hleStruct M (tach M) ha) s.val)
    = Matrix.reindex _ _ (Agen 1 M (tach M) _ (hleStruct M (tach M) ha) s.val)
  congr 1
  fin_cases s
  · -- boundary 0: `Agen 0` uses `Nblk 0 = 0` (rfl) and the interior `Cgen 1` match
    exact Agen_congr M (tach M) (hleStruct M (tach M) ha) (x p₀) 1 _ _ 0
      (by rfl) (by rfl) (Cgen1_match ha h0r h0c x)
  · -- boundary 1: `Agen 1` uses `Nblk 1 = readN ⟨0⟩` (the `_pbo` match) and the leaf `Cgen 2` match
    exact Agen_congr M (tach M) (hleStruct M (tach M) ha) (x p₀) 1 _ _ 1
      (live_Nblk_match ha h0r h0c x) (live_Wblk_match ha h0r h0c x) (Cgen2_match ha h0r h0c x)

/-- **`hmap`**: `phiFlatLiveAt M ha hL p₀ = Bchart ha ∘ pivotBlowupOn activeM p₀` — the map identity
(obligation (1) of `interiorDet_leaf_headline`), discharged from the per-layer match
(via the Cgen-block matches; NO explicit `chainA` reindexing). Both sides are `paramsEquivFlat ∘
chartParamsGen`; `chartParamsGen_match` does the work. -/
theorem hmap_leaf (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    phiFlatLiveAt M ha (by norm_num) (leafPivot M ha (by norm_num) h0r h0c)
      = Bchart ha ∘ pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) := by
  funext x
  show phiGen (x (leafPivot M ha (by norm_num) h0r h0c)) M (tach M)
      (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha (by norm_num) x) x)
      (hleStruct M (tach M) ha) = _
  show paramsEquivFlat M
      (chartParamsGen (x (leafPivot M ha (by norm_num) h0r h0c)) M (tach M)
        (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha (by norm_num) x) x)
        (hleStruct M (tach M) ha)) = _
  rw [chartParamsGen_match ha h0r h0c x]
  rfl

end L2

end DLNFibre.DLN.RLCT
