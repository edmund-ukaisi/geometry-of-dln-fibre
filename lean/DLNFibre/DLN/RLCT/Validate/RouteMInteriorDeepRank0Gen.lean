import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenAtom
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenInj

/-!
# `RouteMInteriorDeepRank0Gen` — the general-`L` `deepRank = 0` interior box-divergence atom

The general-`L` lift of the `Fin (2+1)`-pinned `deepRank = 0` handler
(`RouteMInteriorDeepRank0` / `…Atom`). The DONE general-`L` LIVE-leaf interior atom
(`routeMCore_box_diverges_interiorLiveGen`) covers `InteriorDrop ∧ 0 < deepRank M` — its chart binds
`leafPivot`, which needs `h0r : 0 < Text M (tach M) L` (= `0 < deepRank`). At `deepRank = 0` the leaf
K-block is VACUOUS (`Text L = 0`), `leafPivot` does not exist, and the radial pivot must sit on an
INTERIOR E-active slot.

This module **re-pivots** the DONE `interiorLiveGen` staircase from the leaf pivot to an interior
E-active slot `p₀`, following the L=2 `genBlkFlatEfp` template but reusing the general-`L`
K-diagonal boundary-factor determinant (`interiorLive_BdetMonomialGen`) rather than the L=2
`|det DB| = 1` shortcut (which is FALSE at general `L` — interior K-blocks survive `deepRank = 0`).

The structural key (dr0adj + decorrelated Codex-xhigh, both BOUNDED): `radialComp_abs_det_at` is
FULLY pivot-generic, and the base Jacobian exponent `liveLeafHOnIdxGen` is `0` at every E-role slot
(nonzero only on K-diagonal slots). So the `minAdm − 1` radial override on an E-slot pivot is clean;
the boundary factor det is the SAME K-diagonal product as the leaf-pivot case. The `kLDU`/`pbo`
commute threads via `kLDU`'s E-role identity arm (`kLDU_eq_on_activeMGen`) — cleaner than the leaf
case, since an E-slot pivot IS an active slot.

Axiom profile target: `routeMCore_box_diverges_eDeepRank0Gen` = `[propext, Classical.choice,
Quot.sound, monomial_rlct]` (clean-three + the single S2 cited axiom).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The pivot-generic `kLDU` / `pivotBlowupOn` commute over `activeMGen`

Codex-recommended core abstraction: the commute for ANY radial pivot `p₀ ∈ activeMGen`, not only
`leafPivot`. K-slots are `∉ activeMGen` (hence `≠ p₀` since `p₀ ∈ activeMGen`) and kLDU-active; E/leaf
active slots are fixed by `kLDU_eq_on_activeMGen`. -/

/-- **`readK (pbo x) k = readK x k` for any `p₀ ∈ activeMGen`** — the K-slot is `∉ activeMGen`
(`readKslot_notMem_activeMGen`) and hence `≠ p₀` (`p₀ ∈ activeMGen`), so `pivotBlowupOn` fixes it.
Pivot-generic lift of `readK_pbo_allGen`. -/
theorem readK_pbo_allGen_at (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (p₀ : Fin (routeMAmbient M)) (hp₀ : p₀ ∈ activeMGen M ha) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) (i j : Fin (Text M (tach M) (k.val + 2))) :
    readK M (tach M) ha (pivotBlowupOn (activeMGen M ha) p₀ x) k i j
      = readK M (tach M) ha x k i j := by
  have hnotmem : readKslot M ha k i j ∉ activeMGen M ha := readKslot_notMem_activeMGen M ha k i j
  have hne : readKslot M ha k i j ≠ p₀ := fun h => hnotmem (h ▸ hp₀)
  rw [readK_eq_readKslot, readK_eq_readKslot, pivotBlowupOn, if_neg hne, if_neg hnotmem]

/-- **The `kLDU` / `pivotBlowupOn` commute for any `p₀ ∈ activeMGen`** —
`pbo (kLDU x) = kLDU (pbo x)`. Pivot-generic lift of `interiorLive_commuteGen`. -/
theorem kLDU_pbo_commuteGen_at (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (p₀ : Fin (routeMAmbient M)) (hp₀ : p₀ ∈ activeMGen M ha) (x : Fin (routeMAmbient M) → ℝ) :
    pivotBlowupOn (activeMGen M ha) p₀ (kLDU M (tach M) ha x)
      = kLDU M (tach M) ha (pivotBlowupOn (activeMGen M ha) p₀ x) := by
  funext q
  by_cases hpiv : q = p₀
  · subst hpiv
    rw [pivotBlowupOn, if_pos rfl, kLDU_eq_on_activeMGen M ha x hp₀,
        kLDU_eq_on_activeMGen M ha (pivotBlowupOn (activeMGen M ha) q x) hp₀,
        pivotBlowupOn, if_pos rfl]
  · by_cases hact : q ∈ activeMGen M ha
    · rw [pivotBlowupOn, if_neg hpiv, if_pos hact,
          kLDU_eq_on_activeMGen M ha x hact, kLDU_eq_on_activeMGen M ha x hp₀,
          kLDU_eq_on_activeMGen M ha (pivotBlowupOn (activeMGen M ha) p₀ x) hact,
          pivotBlowupOn, if_neg hpiv, if_pos hact]
    · -- spectator: both kLDU calls land in the same arm; K-arm equal by `readK_pbo_allGen_at`,
      -- identity arm by `pbo` fixing the slot (`q ∉ activeMGen`, `q ≠ p₀`).
      rw [pivotBlowupOn, if_neg hpiv, if_neg hact, kLDU, kLDU]
      have hpboq : pivotBlowupOn (activeMGen M ha) p₀ x q = x q := by
        rw [pivotBlowupOn, if_neg hpiv, if_neg hact]
      match hc : chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL q with
      | ⟨k, Sum.inl s⟩ =>
        have hmat : readK M (tach M) ha (pivotBlowupOn (activeMGen M ha) p₀ x) k
            = readK M (tach M) ha x k := by
          funext a b; exact readK_pbo_allGen_at M ha p₀ hp₀ x k a b
        simp only [hmat, hpboq]
      | ⟨k, Sum.inr s⟩ => simp only [hpboq]

/-! ## Pivot-generic spectator readers (fixed by `pbo p₀`, `p₀ ∈ activeMGen`)

The X/N/W readers place their entry `∉ activeMGen`, so `≠ p₀` (`p₀ ∈ activeMGen`) — hence `pbo p₀`
fixes them, verbatim from the leaf-pivot `readX/N/W_pbo_all` proofs (which are already stated with a
`k ≠ L−1` / lift guard). -/

/-- `readX (pbo p₀ x) k = readX x k` at an interior boundary `k ≠ L−1`, for `p₀ ∈ activeMGen`. -/
theorem readX_pbo_all_at (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (p₀ : Fin (routeMAmbient M)) (hp₀ : p₀ ∈ activeMGen M ha) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) (hk : k.val ≠ L - 1)
    (i : Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
    (j : Fin (Text M (tach M) (k.val + 2))) :
    readX M (tach M) ha (pivotBlowupOn (activeMGen M ha) p₀ x) k i j
      = readX M (tach M) ha x k i j := by
  have hnm : readXslot M ha k i j ∉ activeMGen M ha := readXslot_notMem_activeMGen M ha k hk i j
  have hne : readXslot M ha k i j ≠ p₀ := fun h => hnm (h ▸ hp₀)
  rw [readX_eq_readXslot, readX_eq_readXslot, pivotBlowupOn, if_neg hne, if_neg hnm]

/-- `readN (pbo p₀ x) k = readN x k` at an interior boundary `k ≠ L−1`, for `p₀ ∈ activeMGen`. -/
theorem readN_pbo_all_at (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (p₀ : Fin (routeMAmbient M)) (hp₀ : p₀ ∈ activeMGen M ha) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) (hk : k.val ≠ L - 1)
    (i : Fin (Text M (tach M) (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) :
    readN M (tach M) ha (pivotBlowupOn (activeMGen M ha) p₀ x) k i j
      = readN M (tach M) ha x k i j := by
  have hnm : readNslot M ha k i j ∉ activeMGen M ha := readNslot_notMem_activeMGen M ha k hk i j
  have hne : readNslot M ha k i j ≠ p₀ := fun h => hnm (h ▸ hp₀)
  rw [readN_eq_readNslot, readN_eq_readNslot, pivotBlowupOn, if_neg hne, if_neg hnm]

/-- `readW (pbo p₀ x) k = readW x k` at an interior boundary with a lift (`k.val + 1 < L`), for
`p₀ ∈ activeMGen`. -/
theorem readW_pbo_all_at (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (p₀ : Fin (routeMAmbient M)) (hp₀ : p₀ ∈ activeMGen M ha) (x : Fin (routeMAmbient M) → ℝ)
    (k : Fin L) (hk : k.val + 1 < L)
    (i : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) (j : Fin (Wext M (k.val + 2))) :
    readW M (tach M) ha (pivotBlowupOn (activeMGen M ha) p₀ x) k hk i j
      = readW M (tach M) ha x k hk i j := by
  have hnm : readWslot M ha k hk i j ∉ activeMGen M ha := readWslot_notMem_activeMGen M ha k hk i j
  have hne : readWslot M ha k hk i j ≠ p₀ := fun h => hnm (h ▸ hp₀)
  rw [readW_eq_readWslot, readW_eq_readWslot, pivotBlowupOn, if_neg hne, if_neg hnm]

/-! The E-scaling at the pivot boundary is handled directly by the E-block match `EfixedReaderGen_pboE`
below (which gives `(x p₀) • EfixedReaderGen k x = readE (pbo p₀ x) k` relative to the pivot). At a
NON-pivot interior boundary `k' ≠ k` every E-slot `activeSlotE k' i j` is in `activeMGen` and `≠ p₀`
(distinct boundary tag), so it scales by `x p₀` — the pivot-generic `readE_pbo_all_ne` below. -/

/-! ## The interior E-block pivot at the `InteriorDrop` boundary -/

/-- **The interior E-block pivot** `eBlockPivotGen k = activeSlotE k ⟨0⟩ ⟨0⟩` at an interior boundary
`k ≠ L−1` with a nonempty E-block. The radial binding axis at `deepRank = 0`. -/
noncomputable def eBlockPivotGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2)) : Fin (routeMAmbient M) :=
  activeSlotE M (tach M) ha k ⟨0, hr⟩ ⟨0, hc⟩

/-- **`eBlockPivotGen ∈ activeMGen`** (an E-block slot at an interior boundary). -/
theorem eBlockPivotGen_mem_activeMGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2)) :
    eBlockPivotGen M ha k hr hc ∈ activeMGen M ha :=
  activeSlotE_mem_activeMGen M ha k hk ⟨0, hr⟩ ⟨0, hc⟩

/-- **An E-slot at a boundary `k' ≠ k` is `≠ eBlockPivotGen k`** — distinct `chartIdxEquiv` boundary
tags (`activeSlotE_chartIdx_fst`). -/
theorem activeSlotE_ne_eBlockPivotGen_of_boundary_ne (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (k k' : Fin L) (hkk' : k' ≠ k)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (i : Fin (Text M (tach M) (k'.val + 1) - Text M (tach M) (k'.val + 2)))
    (j : Fin (Wext M (k'.val + 1) - Text M (tach M) (k'.val + 2))) :
    activeSlotE M (tach M) ha k' i j ≠ eBlockPivotGen M ha k hr hc := by
  intro h
  have h1 : ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL) (activeSlotE M (tach M) ha k' i j)).1
      = k' := activeSlotE_chartIdx_fst M (tach M) ha k' i j
  have h2 : ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL)
      (eBlockPivotGen M ha k hr hc)).1 = k :=
    activeSlotE_chartIdx_fst M (tach M) ha k ⟨0, hr⟩ ⟨0, hc⟩
  rw [h] at h1; rw [h1] at h2; exact hkk' h2

/-- **`readE (pbo p₀ x) k' = (x p₀) · readE x k'` at a boundary `k' ≠ k`** (`k' ≠ L−1`), where
`p₀ = eBlockPivotGen k`. Every E-slot at `k'` is in `activeMGen` and `≠ p₀` (distinct boundary), so
`pbo` scales it. -/
theorem readE_pbo_all_ne (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k k' : Fin L)
    (hkk' : k' ≠ k) (hk' : k'.val ≠ L - 1)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (x : Fin (routeMAmbient M) → ℝ)
    (i : Fin (Text M (tach M) (k'.val + 1) - Text M (tach M) (k'.val + 2)))
    (j : Fin (Wext M (k'.val + 1) - Text M (tach M) (k'.val + 2))) :
    readE M (tach M) ha (pivotBlowupOn (activeMGen M ha) (eBlockPivotGen M ha k hr hc) x) k' i j
      = x (eBlockPivotGen M ha k hr hc) * readE M (tach M) ha x k' i j := by
  have hslot : readE M (tach M) ha (pivotBlowupOn (activeMGen M ha) (eBlockPivotGen M ha k hr hc) x) k' i j
      = pivotBlowupOn (activeMGen M ha) (eBlockPivotGen M ha k hr hc) x
          (activeSlotE M (tach M) ha k' i j) := rfl
  rw [hslot, pivotBlowupOn,
    if_neg (activeSlotE_ne_eBlockPivotGen_of_boundary_ne M ha k k' hkk' hr hc i j),
    if_pos (activeSlotE_mem_activeMGen M ha k' hk' i j)]
  rfl

/-- **A non-pivot E-slot `(i,j) ≠ (0,0)` is `≠ eBlockPivotGen`** (`activeSlotE` injective in `(i,j)`). -/
theorem activeSlotE_ne_eBlockPivotGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (i : Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) (hij : ¬ (i.val = 0 ∧ j.val = 0)) :
    activeSlotE M (tach M) ha k i j ≠ eBlockPivotGen M ha k hr hc := by
  rw [eBlockPivotGen]
  intro h
  obtain ⟨hi, hj⟩ := activeSlotE_inj M (tach M) ha k h
  exact hij ⟨by simp [hi], by simp [hj]⟩

/-! ## The E-fixed-pivot decoder (general `L`) -/

/-- **The E-fixed-pivot reader** at boundary `k` — the E-block residual with the pivot `(0,0)` entry
pinned to the radial fixed `1`, other entries read live via `readE`. General-`L` lift of the L=2
`EfixedReader`. -/
noncomputable def EfixedReaderGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (x : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
      (Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) ℝ :=
  Matrix.of fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1 else readE M (tach M) ha x k i j

/-- **The E-fixed-pivot radial identity** — the load-bearing E-block match:
`(x p₀) • EfixedReaderGen k x = readE (pbo p₀ x) k` (as matrices), where `p₀ = eBlockPivotGen k`.
At the pivot `(0,0)`: `(x p₀)·1 = (pbo x) p₀ = x p₀`; off `(0,0)`: `(x p₀)·(readE x) =
(pbo x)(activeSlotE i j) = x p₀ · x slot` (pbo scales the active non-pivot E-slot). General-`L`
lift of the L=2 `EfixedReader_pboE`. -/
theorem EfixedReaderGen_pboE (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (x : Fin (routeMAmbient M) → ℝ) :
    (x (eBlockPivotGen M ha k hr hc)) • EfixedReaderGen M ha k x
      = (fun i j => readE M (tach M) ha
          (pivotBlowupOn (activeMGen M ha) (eBlockPivotGen M ha k hr hc) x) k i j) := by
  set p₀ := eBlockPivotGen M ha k hr hc with hp₀
  funext i j
  rw [Matrix.smul_apply, smul_eq_mul, EfixedReaderGen, Matrix.of_apply]
  -- both readE slots ARE `x (activeSlotE k i j)` (defeq)
  have hslot : readE M (tach M) ha (pivotBlowupOn (activeMGen M ha) p₀ x) k i j
      = pivotBlowupOn (activeMGen M ha) p₀ x (activeSlotE M (tach M) ha k i j) := rfl
  rw [hslot]
  by_cases hij : i.val = 0 ∧ j.val = 0
  · -- the pivot entry: LHS `= x p₀ · 1`; RHS `= (pbo x) p₀ = x p₀`
    obtain ⟨hi, hj⟩ := hij
    have hi' : i = ⟨0, hr⟩ := Fin.ext hi
    have hj' : j = ⟨0, hc⟩ := Fin.ext hj
    subst hi' hj'
    rw [if_pos ⟨rfl, rfl⟩, mul_one]
    show x p₀ = pivotBlowupOn (activeMGen M ha) p₀ x (activeSlotE M (tach M) ha k ⟨0, hr⟩ ⟨0, hc⟩)
    rw [show activeSlotE M (tach M) ha k ⟨0, hr⟩ ⟨0, hc⟩ = p₀ from rfl,
      pivotBlowupOn, if_pos rfl]
  · -- a non-pivot E-entry: LHS `= x p₀ · readE x`; RHS `= (pbo x)(slot) = x p₀ · x slot`
    rw [if_neg hij]
    have hslotx : readE M (tach M) ha x k i j = x (activeSlotE M (tach M) ha k i j) := rfl
    rw [hslotx, pivotBlowupOn, if_neg (activeSlotE_ne_eBlockPivotGen M ha k hr hc i j hij),
      if_pos (activeSlotE_mem_activeMGen M ha k hk i j)]

/-- **The E-fixed-pivot decoder** `genBlkFlatEfpGen k` — the live decoder (`rfin = 0`, leaf empty at
`deepRank = 0`) with the pivot-boundary `k+1`'s `Rmat` overridden to `rmatPad (EfixedReaderGen k x)`.
General-`L` lift of `genBlkFlatEfp`. -/
noncomputable def genBlkFlatEfpGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (x : Fin (routeMAmbient M) → ℝ) : GenBlk M (tach M) where
  Bmat := (genBlkFlatLive M (tach M) ha 0 x).Bmat
  Nblk := (genBlkFlatLive M (tach M) ha 0 x).Nblk
  Wblk := (genBlkFlatLive M (tach M) ha 0 x).Wblk
  Rmat := Function.update (genBlkFlatLive M (tach M) ha 0 x).Rmat (k.val + 1)
    (rmatPad M (tach M) (k.val + 1) hp1 hp2 (EfixedReaderGen M ha k x))
  Rfin := (genBlkFlatLive M (tach M) ha 0 x).Rfin

/-! ## The deepRank = 0 chart + rate

Following the DONE `interiorLivePhiGen x = phiFlatLiveAt … leafPivot (kLDU x)`: the E-fixed chart
composes `kLDU` on the input so the boundary-factor det is the K-diagonal monomial. The radial slot
`p₀` survives `kLDU` (`p₀ ∈ activeMGen`, `kLDU_eq_on_activeMGen`). -/

/-- **The E-fixed chart at an arbitrary point** `phiEfpAt k p₀ y := phiGen (y p₀) … (genBlkFlatEfpGen k y)`.
The composed chart is `phiEfpAt k p₀ (kLDU x)`. -/
noncomputable def phiEfpAt (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (y : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ :=
  phiGen (y p₀) M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 y) (hleStruct M (tach M) ha)

/-- **The deepRank = 0 chart** at pivot boundary `k`, radial slot `p₀`:
`phiEfpAt k p₀ (kLDU x)`. General-`L` lift of `eDeepRank0Phi`, kLDU-composed like `interiorLivePhiGen`. -/
noncomputable def eDeepRank0PhiGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) :=
  fun x => phiEfpAt M ha k p₀ hp1 hp2 (kLDU M (tach M) ha x)

/-- **The deepRank = 0 unit factor** `eDeepRank0UnitGen x := VvalGen (x p₀) … (genBlkFlatEfpGen k (kLDU x))`.
The radial slot `p₀ ∈ activeMGen` survives `kLDU` (`(kLDU x) p₀ = x p₀`), so the radial scalar is `x p₀`. -/
noncomputable def eDeepRank0UnitGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    (Fin (routeMAmbient M) → ℝ) → ℝ :=
  fun x => VvalGen (x p₀) M (tach M)
    (genBlkFlatEfpGen M ha k hp1 hp2 (kLDU M (tach M) ha x)) (hleStruct M (tach M) ha)

/-- **The single-axis Jacobian exponent vector** — `minAdm − 1` at the pivot `p₀`, `liveLeafHOnIdxGen`
elsewhere. The E-slot pivot's base `liveLeafHOnIdxGen` exponent is `0`, so the radial `minAdm − 1`
override is clean; the K-diagonal exponents (`liveLeafHOnIdxGen`) survive at their slots. -/
noncomputable def eDeepRank0_leafHGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (p₀ : Fin (routeMAmbient M)) : Fin (routeMAmbient M) → ℕ := fun j =>
  if j = p₀ then minAdm M - 1
  else liveLeafHOnIdxGen M ha (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL j)

/-- **The binding axis carries `minAdm − 1`** (`if_pos rfl`). -/
theorem eDeepRank0_leafHGen_pivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (p₀ : Fin (routeMAmbient M)) :
    eDeepRank0_leafHGen M ha p₀ p₀ = minAdm M - 1 := by
  rw [eDeepRank0_leafHGen, if_pos rfl]

/-! ## The identity-boundary `hC0` for the E-fixed decoder (general `L`) -/

/-- The Efp decoder's identity boundary `Rmat 0 = 0` (`Function.update` at `k+1 ≥ 1` misses `0`). -/
theorem genBlkFlatEfpGen_Rmat0 (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatEfpGen M ha k hp1 hp2 x).Rmat 0
      = (0 : Matrix (Fin (Text M (tach M) 0)) (Fin (Wext M 0)) ℝ) := by
  change Function.update (genBlkFlatLive M (tach M) ha 0 x).Rmat (k.val + 1)
    (rmatPad M (tach M) (k.val + 1) hp1 hp2 (EfixedReaderGen M ha k x)) 0 = _
  rw [Function.update_of_ne (Ne.symm (Nat.succ_ne_zero k.val))]
  exact genBlkFlatLive_Rmat0 M (tach M) ha 0 x

/-- **The identity boundary `C 0 = 1`** for the E-fixed decoder — reads only `Bmat 0`/`Rmat 0`, both as
in the live decoder (`Bmat 0 = reindex 1`; `Rmat 0 = 0` since the `Function.update` at `k+1` misses `0`).
Proof verbatim from `C0_eq_one_liveR1`. -/
theorem C0_eq_one_EfpGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 x) (hleStruct M (tach M) ha)).toChain.C 0
      = (1 : Matrix (Fin (Text M (tach M) 0)) (Fin (Text M (tach M) 0)) ℝ) := by
  rw [chainOfMt_C_zero v M (tach M) _ (hleStruct M (tach M) ha) ha.hL,
    genBlkFlatEfpGen_Rmat0 M ha k hp1 hp2 x, smul_zero, add_zero]
  have hBmat : (genBlkFlatEfpGen M ha k hp1 hp2 x).Bmat 0
      = Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1_struct M (tach M) ha.h0))
          (1 : Matrix (Fin (Text M (tach M) 0)) (Fin (Text M (tach M) 0)) ℝ) := rfl
  have h1W : Text M (tach M) 1 = Wext M 0 := Wext0_eq_Text1 M (tach M) ha
  rw [hBmat]
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.cast (Text0_eq_Text1_struct M (tach M) ha.h0) i)]
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Matrix.one_apply_eq, one_mul]
    have hjcol : (j : Fin (Wext M 0)) = Fin.cast (genWidthEq M (tach M) (hleStruct M (tach M) ha) 0 ha.hL)
        (Fin.castAdd (Wext M 0 - Text M (tach M) (0 + 1)) (Fin.cast h1W.symm j)) := by
      apply Fin.ext; simp
    rw [hjcol, chainQ_apply_castAdd, Matrix.one_apply, Matrix.one_apply]
    by_cases h : (i : ℕ) = (j : ℕ)
    · rw [if_pos (by apply Fin.ext; simpa using h), if_pos (by apply Fin.ext; simpa using h)]
    · rw [if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc)),
        if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc))]
  · intro b _ hb
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply]
    rw [show (1 : Matrix (Fin (Text M (tach M) 0)) (Fin (Text M (tach M) 0)) ℝ) i
          (Fin.cast (Text0_eq_Text1_struct M (tach M) ha.h0).symm b) = 0 from by
      rw [Matrix.one_apply, if_neg]; intro hc; apply hb; rw [hc]; apply Fin.ext; simp]
    rw [zero_mul]
  · intro hi; exact absurd (Finset.mem_univ _) hi

/-- **`hC0` for the E-fixed decoder** (`C 0 · suffix = suffix` from `C 0 = 1`). -/
theorem hC0_EfpGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 x) (hleStruct M (tach M) ha)).toChain.C 0
        * (chainOfMt v M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 x)
            (hleStruct M (tach M) ha)).toChain.suffix 0 (Nat.zero_le L)
      = (chainOfMt v M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 x)
          (hleStruct M (tach M) ha)).toChain.suffix 0 (Nat.zero_le L) := by
  rw [C0_eq_one_EfpGen M ha k hp1 hp2 v x]; exact Matrix.one_mul _

/-! ## The rate -/

/-- **The rate of `phiEfpAt`** `routeMCore M (phiEfpAt k p₀ y) = (y p₀)² · VvalGen …`. Via
`routeMCore_phiGen` + the E-fixed identity boundary `hC0_EfpGen`. -/
theorem routeMCore_phiEfpAt (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (y : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (phiEfpAt M ha k p₀ hp1 hp2 y)
      = (y p₀) ^ 2
        * VvalGen (y p₀) M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 y) (hleStruct M (tach M) ha) :=
  routeMCore_phiGen (y p₀) M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 y) (hleStruct M (tach M) ha)
    (hC0_EfpGen M ha k hp1 hp2 (y p₀) y)

/-- **The deepRank = 0 rate via the unit** `routeMCore M (eDeepRank0PhiGen x) = (x p₀)² · eDeepRank0UnitGen x`.
The radial slot `p₀ ∈ activeMGen` survives `kLDU` (`kLDU_eq_on_activeMGen`), so `(kLDU x) p₀ = x p₀`. -/
theorem routeMCore_eDeepRank0PhiGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M)) (hp₀ : p₀ ∈ activeMGen M ha)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (eDeepRank0PhiGen M ha k p₀ hp1 hp2 x)
      = (x p₀) ^ 2 * eDeepRank0UnitGen M ha k p₀ hp1 hp2 x := by
  rw [eDeepRank0PhiGen, routeMCore_phiEfpAt M ha k p₀ hp1 hp2 (kLDU M (tach M) ha x),
    kLDU_eq_on_activeMGen M ha x hp₀]
  rfl

/-- `0 ≤ eDeepRank0UnitGen` (sum of squares, banked `VvalGen_nonneg`). -/
theorem eDeepRank0UnitGen_nonneg (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (x : Fin (routeMAmbient M) → ℝ) :
    0 ≤ eDeepRank0UnitGen M ha k p₀ hp1 hp2 x :=
  VvalGen_nonneg _ M (tach M) _ _

/-! ## The map factorization `hmap_EfpGen` (the CAREFUL SPOT — E-slot pivot)

`phiEfpAt k p₀ y = BchartLeafGen (pbo p₀ y)` where `p₀ = eBlockPivotGen k`. Both sides are
`paramsEquivFlat ∘ chartParamsGen`; the per-layer chart-param match (`Agen_congr`) reduces to the
`Nblk`/`Wblk`/`Cgen(s+1)` matches. The genuine content: at the PIVOT boundary `k+1` the Efp decoder
reads `EfixedReaderGen k` (fixed-`1` pivot) which matches the direct `readE (pbo y)` via the radial
identity `EfixedReaderGen_pboE`; at OTHER interior boundaries the E-block reads live `readE`, matching
`readE (pbo y)` scaled — but the DIRECT chart `BchartLeafGen` reads `readE (pbo y)` at radial `1`, so
BOTH boundaries use `schurFrameProd_u_to_E` to move the radial `u = y p₀` into the residual coordinate. -/

/-- The Efp decoder's `Bmat (s+1)` (`s < L`) is the live/struct decoder's. -/
theorem genBlkFlatEfpGen_Bmat_succ (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (x : Fin (routeMAmbient M) → ℝ) (s : ℕ) (hs : s < L) :
    (genBlkFlatEfpGen M ha k hp1 hp2 x).Bmat (s + 1)
      = bmatStack M (tach M) (s + 1) (ha.hdesc s hs)
          (readK M (tach M) ha x ⟨s, hs⟩) (readX M (tach M) ha x ⟨s, hs⟩) :=
  genBlkFlatLive_Bmat_succ M (tach M) ha 0 x s hs

/-- The Efp decoder's `Nblk (s+1)` (`s < L`) is `readN ⟨s⟩`. -/
theorem genBlkFlatEfpGen_Nblk_succ (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (x : Fin (routeMAmbient M) → ℝ) (s : ℕ) (hs : s < L) :
    (genBlkFlatEfpGen M ha k hp1 hp2 x).Nblk (s + 1) = readN M (tach M) ha x ⟨s, hs⟩ :=
  genBlkFlatLive_Nblk_succ M (tach M) ha 0 x s hs

/-- The Efp decoder's `Rmat` at the pivot boundary `k+1` IS `rmatPad (EfixedReaderGen k x)`. -/
theorem genBlkFlatEfpGen_Rmat_pivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatEfpGen M ha k hp1 hp2 x).Rmat (k.val + 1)
      = rmatPad M (tach M) (k.val + 1) hp1 hp2 (EfixedReaderGen M ha k x) := by
  change Function.update (genBlkFlatLive M (tach M) ha 0 x).Rmat (k.val + 1)
    (rmatPad M (tach M) (k.val + 1) hp1 hp2 (EfixedReaderGen M ha k x)) (k.val + 1) = _
  rw [Function.update_self]

/-- The Efp decoder's `Rmat` at a NON-pivot boundary `s ≠ k+1` is the live/struct decoder's. -/
theorem genBlkFlatEfpGen_Rmat_ne (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (x : Fin (routeMAmbient M) → ℝ) (s : ℕ) (hs : s ≠ k.val + 1) :
    (genBlkFlatEfpGen M ha k hp1 hp2 x).Rmat s = (genBlkFlatLive M (tach M) ha 0 x).Rmat s := by
  change Function.update (genBlkFlatLive M (tach M) ha 0 x).Rmat (k.val + 1)
    (rmatPad M (tach M) (k.val + 1) hp1 hp2 (EfixedReaderGen M ha k x)) s = _
  rw [Function.update_of_ne hs]

/-- The Efp decoder's `Cgen` at the PIVOT boundary `k+1` (`k+1 < L`) is the Schur frame with
`E = EfixedReaderGen k x`. -/
theorem Cgen_EfpGen_pivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hkL : k.val + 1 < L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    Cgen v M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 x) (hleStruct M (tach M) ha) (k.val + 1)
      = schurFrameProd M (tach M) (k.val + 1) (ha.hdesc k.val (by omega)) (ha.hub k.val) v
          (readK M (tach M) ha x ⟨k.val, by omega⟩) (readX M (tach M) ha x ⟨k.val, by omega⟩)
          (readN M (tach M) ha x ⟨k.val, by omega⟩) (EfixedReaderGen M ha k x) := by
  rw [Cgen, dif_pos hkL, genBlkFlatEfpGen_Bmat_succ M ha k hp1 hp2 x k.val (by omega),
    genBlkFlatEfpGen_Nblk_succ M ha k hp1 hp2 x k.val (by omega),
    genBlkFlatEfpGen_Rmat_pivot M ha k hp1 hp2 x, schurFrameProd]

/-- The Efp decoder's `Cgen` at a NON-pivot interior boundary `s+1 ≠ k+1` (`s+1 < L`) is the Schur
frame with `E = readE ⟨s⟩` (live, `Function.update` misses this boundary). -/
theorem Cgen_EfpGen_nonpivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) (s : ℕ) (hs1 : s + 1 < L) (hne : s + 1 ≠ k.val + 1) :
    Cgen v M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 x) (hleStruct M (tach M) ha) (s + 1)
      = schurFrameProd M (tach M) (s + 1) (ha.hdesc s (by omega)) (ha.hub s) v
          (readK M (tach M) ha x ⟨s, by omega⟩) (readX M (tach M) ha x ⟨s, by omega⟩)
          (readN M (tach M) ha x ⟨s, by omega⟩) (readE M (tach M) ha x ⟨s, by omega⟩) := by
  rw [Cgen, dif_pos hs1, genBlkFlatEfpGen_Bmat_succ M ha k hp1 hp2 x s (by omega),
    genBlkFlatEfpGen_Nblk_succ M ha k hp1 hp2 x s (by omega),
    genBlkFlatEfpGen_Rmat_ne M ha k hp1 hp2 x (s + 1) hne,
    genBlkFlatLive_Rmat_succ M (tach M) ha 0 x s (by omega), schurFrameProd]

/-! ### The `Nblk` / `Wblk` matches (spectator, under `pbo p₀`) -/

/-- The Efp `Nblk (j+1)` matches the direct `BchartLeafGen`-decoder's under `pbo p₀` (spectator). -/
theorem live_Nblk_matchEGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M)) (hp₀ : p₀ ∈ activeMGen M ha)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (x : Fin (routeMAmbient M) → ℝ) (j : ℕ) (hj1 : j + 1 < L) :
    (genBlkFlatEfpGen M ha k hp1 hp2 x).Nblk (j + 1)
      = (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha
          (pivotBlowupOn (activeMGen M ha) p₀ x))
          (pivotBlowupOn (activeMGen M ha) p₀ x)).Nblk (j + 1) := by
  have hjL : j < L := by omega
  have hjne : (⟨j, hjL⟩ : Fin L).val ≠ L - 1 := by show j ≠ L - 1; omega
  rw [genBlkFlatEfpGen_Nblk_succ M ha k hp1 hp2 x j hjL,
    genBlkFlatLive_Nblk_succ M (tach M) ha _ _ j hjL]
  funext i c; exact (readN_pbo_all_at M ha p₀ hp₀ x ⟨j, hjL⟩ hjne i c).symm

/-- The Efp `Wblk (j+1)` matches the direct `BchartLeafGen`-decoder's under `pbo p₀` (spectator). -/
theorem live_Wblk_matchEGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M)) (hp₀ : p₀ ∈ activeMGen M ha)
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (x : Fin (routeMAmbient M) → ℝ) (j : ℕ) (hj1 : j + 1 < L) :
    (genBlkFlatEfpGen M ha k hp1 hp2 x).Wblk (j + 1)
      = (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha
          (pivotBlowupOn (activeMGen M ha) p₀ x))
          (pivotBlowupOn (activeMGen M ha) p₀ x)).Wblk (j + 1) := by
  have hjL : j < L := by omega
  show (genBlkFlatStruct M (tach M) ha x).Wblk (j + 1)
    = (genBlkFlatStruct M (tach M) ha (pivotBlowupOn (activeMGen M ha) p₀ x)).Wblk (j + 1)
  simp only [genBlkFlatStruct, dif_pos hjL, dif_pos hj1]
  funext i c; exact (readW_pbo_all_at M ha p₀ hp₀ x ⟨j, hjL⟩ hj1 i c).symm

/-! ### The Cgen matches (per boundary) under `pbo p₀` -/

/-- **The interior `Cgen (s+1 < L)` match** — the Efp decoder's transition at interior boundary `s+1`
(radial `x p₀`) equals the direct `BchartLeafGen`-decoder's (radial `1`) under `pbo p₀`. At the PIVOT
boundary `s+1 = k+1` the E-block is `EfixedReaderGen` matched via `EfixedReaderGen_pboE`; at OTHER
interior boundaries the E-block reads live `readE`, matched via `readE_pbo_all`. Both fold the radial
`u = x p₀` into the residual coordinate (`schurFrameProd_u_to_E`). -/
theorem Cgen_interior_matchEGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (x : Fin (routeMAmbient M) → ℝ) (s : ℕ) (hs1 : s + 1 < L) :
    Cgen (x (eBlockPivotGen M ha k hr hc)) M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 x)
        (hleStruct M (tach M) ha) (s + 1)
      = Cgen 1 M (tach M)
        (genBlkFlatLive M (tach M) ha
          (rfinDirectGen M ha (pivotBlowupOn (activeMGen M ha) (eBlockPivotGen M ha k hr hc) x))
          (pivotBlowupOn (activeMGen M ha) (eBlockPivotGen M ha k hr hc) x))
        (hleStruct M (tach M) ha) (s + 1) := by
  set p₀ := eBlockPivotGen M ha k hr hc with hp₀
  have hp₀mem : p₀ ∈ activeMGen M ha := eBlockPivotGen_mem_activeMGen M ha k hk hr hc
  set pbo := pivotBlowupOn (activeMGen M ha) p₀ with hpbo
  have hsL : s < L := by omega
  have hsne : (⟨s, hsL⟩ : Fin L).val ≠ L - 1 := by show s ≠ L - 1; omega
  -- rewrite the RHS (direct decoder, radial 1) into `schurFrameProd 1 (readK (pbo x)) …`.
  rw [Cgen_live_interior_eq_schurFrameProd M (tach M) ha _ _ (pbo x) s (by omega)]
  by_cases hsk : s = k.val
  · -- the PIVOT boundary: LHS E = EfixedReaderGen, matched via EfixedReaderGen_pboE.
    -- eliminate `s = k.val`; the reads at `⟨k.val, _⟩` are defeq to those at `k`.
    subst hsk
    rw [Cgen_EfpGen_pivot M ha k (by omega) hp1 hp2 (x p₀) x,
      schurFrameProd_u_to_E M (tach M) (k.val + 1) _ _ (x p₀)]
    -- the RHS reads at `⟨k.val, _⟩` are defeq to those at `k` (Fin.mk proof irrelevance).
    congr 1
    · funext i j; exact (readK_pbo_allGen_at M ha p₀ hp₀mem x k i j).symm
    · funext i j; exact (readX_pbo_all_at M ha p₀ hp₀mem x k hk i j).symm
    · funext i j; exact (readN_pbo_all_at M ha p₀ hp₀mem x k hk i j).symm
    · exact EfixedReaderGen_pboE M ha k hk hr hc x
  · -- a NON-pivot interior boundary `s ≠ k`: LHS E = readE (live), matched via readE_pbo_all_ne.
    rw [Cgen_EfpGen_nonpivot M ha k hp1 hp2 (x p₀) x s (by omega) (by omega),
      schurFrameProd_u_to_E M (tach M) (s + 1) _ _ (x p₀)]
    congr 1
    · funext i j; exact (readK_pbo_allGen_at M ha p₀ hp₀mem x ⟨s, hsL⟩ i j).symm
    · funext i j; exact (readX_pbo_all_at M ha p₀ hp₀mem x ⟨s, hsL⟩ hsne i j).symm
    · funext i j; exact (readN_pbo_all_at M ha p₀ hp₀mem x ⟨s, hsL⟩ hsne i j).symm
    · funext i j
      rw [Matrix.smul_apply, smul_eq_mul,
        readE_pbo_all_ne M ha k ⟨s, hsL⟩ (fun h => hsk (by simpa using congrArg Fin.val h)) hsne
          hr hc x i j]

/-- At `deepRank = 0` (`Text L = 0`) the leaf reader is the empty `0×Wext(L)` matrix. -/
theorem rfinDirectGen_eq_zero_of_hdr0 (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hdr0 : Text M (tach M) L = 0) (y : Fin (routeMAmbient M) → ℝ) :
    rfinDirectGen M ha y = 0 := by
  haveI : IsEmpty (Fin (Text M (tach M) L)) := by rw [hdr0]; infer_instance
  ext i j
  exact isEmptyElim i

/-- **The leaf `Cgen L` match** at `deepRank = 0`: both leaf residuals are the empty `0×Wext(L)` matrix.
The Efp decoder's leaf `Rfin L = 0`; the direct decoder's `rfinDirectGen (pbo x) = 0` (`hdr0`). -/
theorem Cgen_leaf_matchEGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hdr0 : Text M (tach M) L = 0)
    (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (v v' : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    Cgen v M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 x) (hleStruct M (tach M) ha) L
      = Cgen v' M (tach M)
        (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha (pivotBlowupOn (activeMGen M ha) p₀ x))
          (pivotBlowupOn (activeMGen M ha) p₀ x))
        (hleStruct M (tach M) ha) L := by
  rw [Cgen, dif_neg (lt_irrefl L), Cgen, dif_neg (lt_irrefl L)]
  haveI : IsEmpty (Fin (Text M (tach M) L)) := by rw [hdr0]; infer_instance
  ext i j
  exact isEmptyElim i

/-! ### The chart-parameter match + `hmap` -/

/-- **The chart-parameter match** `chartParamsGen (x p₀) (genBlkFlatEfpGen k x) = BparamsLeafGen (pbo x)`
per layer `s : Fin L`, via `Agen_congr`. Layer `s` reads `Nblk`/`Wblk` (spectator matches) and
`Cgen (s+1)` (interior match for `s+1 < L`, leaf match for `s+1 = L`). -/
theorem chartParamsGen_matchEGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1) (hdr0 : Text M (tach M) L = 0)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (x : Fin (routeMAmbient M) → ℝ) :
    chartParamsGen (x (eBlockPivotGen M ha k hr hc)) M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 x)
        (hleStruct M (tach M) ha)
      = BparamsLeafGen M ha (pivotBlowupOn (activeMGen M ha) (eBlockPivotGen M ha k hr hc) x) := by
  set p₀ := eBlockPivotGen M ha k hr hc with hp₀
  have hp₀mem : p₀ ∈ activeMGen M ha := eBlockPivotGen_mem_activeMGen M ha k hk hr hc
  set pbo := pivotBlowupOn (activeMGen M ha) p₀ with hpbo
  rw [BparamsLeafGen]
  funext s
  show Matrix.reindex _ _ (Agen (x p₀) M (tach M) _ (hleStruct M (tach M) ha) s.val)
    = Matrix.reindex _ _ (Agen 1 M (tach M) _ (hleStruct M (tach M) ha) s.val)
  congr 1
  have hN : (genBlkFlatEfpGen M ha k hp1 hp2 x).Nblk s.val
      = (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha (pbo x)) (pbo x)).Nblk s.val := by
    match hsv : s.val with
    | 0 => rfl
    | (j + 1) =>
      have hj1 : j + 1 < L := by have := s.isLt; omega
      exact live_Nblk_matchEGen M ha k p₀ hp₀mem hp1 hp2 x j hj1
  have hW : (genBlkFlatEfpGen M ha k hp1 hp2 x).Wblk s.val
      = (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha (pbo x)) (pbo x)).Wblk s.val := by
    match hsv : s.val with
    | 0 => rfl
    | (j + 1) =>
      have hj1 : j + 1 < L := by have := s.isLt; omega
      exact live_Wblk_matchEGen M ha k p₀ hp₀mem hp1 hp2 x j hj1
  have hC : Cgen (x p₀) M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 x)
        (hleStruct M (tach M) ha) (s.val + 1)
      = Cgen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha (pbo x)) (pbo x))
        (hleStruct M (tach M) ha) (s.val + 1) := by
    by_cases hsL : s.val + 1 < L
    · exact Cgen_interior_matchEGen M ha k hk hr hc hp1 hp2 x s.val hsL
    · have hsL' : s.val + 1 = L := by have := s.isLt; omega
      rw [hsL']
      exact Cgen_leaf_matchEGen M ha k hdr0 p₀ hp1 hp2 (x p₀) 1 x
  exact Agen_congr M (tach M) (hleStruct M (tach M) ha) (x p₀) 1 _ _ s.val hN hW hC

/-- **`hmap_EfpGen`** — `phiEfpAt k p₀ y = BchartLeafGen (pbo p₀ y)` (`p₀ = eBlockPivotGen k`), from
`chartParamsGen_matchEGen`. Both sides are `paramsEquivFlat ∘ chartParamsGen`. -/
theorem hmap_EfpGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1) (hdr0 : Text M (tach M) L = 0)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    phiEfpAt M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2
      = BchartLeafGen M ha ∘ pivotBlowupOn (activeMGen M ha) (eBlockPivotGen M ha k hr hc) := by
  funext x
  show phiGen (x (eBlockPivotGen M ha k hr hc)) M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 x)
      (hleStruct M (tach M) ha) = _
  show paramsEquivFlat M
      (chartParamsGen (x (eBlockPivotGen M ha k hr hc)) M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 x)
        (hleStruct M (tach M) ha)) = _
  rw [chartParamsGen_matchEGen M ha k hk hdr0 hr hc hp1 hp2 x]
  rfl

/-! ## The chart Jacobian abs-det (the K-diagonal monomial, pivot-generic reuse)

The boundary-factor det `|det D(BchartLeafGen ∘ kLDU)(pbo p₀ u)|` is the SAME K-diagonal product as the
leaf-pivot case (`Dtot_factor1_pbo` × `kLDU_ambient_det_pbo_gen`): the K-slots are `∉ activeMGen`, fixed
by ANY `pbo p₀` (`readK_pbo_allGen_at`). We re-thread the two det factors + the collapse with the E-slot
pivot `p₀`, then the `radialComp_abs_det_at` radial split gives `|u p₀|^{minAdm−1}·(K-diagonal product)`. -/

/-- **Factor 1 at `kLDU(pbo p₀ u)`** — `|det D(BchartLeafGen)(kLDU(pbo p₀ u))| =
∏_s |∏_i u (diagAxisGen s i)|^{r_s + c_s}` for any `p₀ ∈ activeMGen`. Pivot-generic lift of
`Dtot_factor1_pbo` (K-diagonal pbo-fix via `readK_pbo_allGen_at`). -/
theorem Dtot_factor1_pbo_at (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (p₀ : Fin (routeMAmbient M)) (hp₀ : p₀ ∈ activeMGen M ha) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (BchartLeafGen M ha)
        (kLDU M (tach M) ha (pivotBlowupOn (activeMGen M ha) p₀ u))).toLinearMap|
      = ∏ s : Fin L, |∏ i, u (diagAxisGen M ha s i)|
          ^ ((Text M (tach M) (s.val + 1) - Text M (tach M) (s.val + 2))
            + (Wext M (s.val + 1) - Text M (tach M) (s.val + 2))) := by
  set z := pivotBlowupOn (activeMGen M ha) p₀ u with hz
  have hDtot : |LinearMap.det (fderiv ℝ (BchartLeafGen M ha) (kLDU M (tach M) ha z)).toLinearMap|
      = |LinearMap.det (DtotGen M ha (kLDU M (tach M) ha z))| := rfl
  rw [hDtot, DtotGen_abs_det M ha (kLDU M (tach M) ha z)]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  congr 1
  have hK : (Matrix.of (readK M (tach M) ha (kLDU M (tach M) ha z) s))
      = kLens (Matrix.of (readK M (tach M) ha z s)) := by
    ext i j; rw [Matrix.of_apply, readK_kLDU]; rfl
  rw [hK, kLens_det]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  show (Matrix.of (readK M (tach M) ha z s)) i i = u (diagAxisGen M ha s i)
  rw [Matrix.of_apply, u_diagAxisGen M ha u s i, hz]
  exact readK_pbo_allGen_at M ha p₀ hp₀ u s i i

/-- **Factor 2 at `pbo p₀ u`** — `|det D(kLDU)(pbo p₀ u)| =
∏_k ∏_i |u (diagAxisGen k i)|^{2(t_k−1−i)}` for any `p₀ ∈ activeMGen`. Pivot-generic lift of
`kLDU_ambient_det_pbo_gen`. -/
theorem kLDU_ambient_det_pbo_gen_at (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (p₀ : Fin (routeMAmbient M)) (hp₀ : p₀ ∈ activeMGen M ha) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (kLDU M (tach M) ha)
        (pivotBlowupOn (activeMGen M ha) p₀ u)).toLinearMap|
      = ∏ k : Fin L, ∏ i : Fin (Text M (tach M) (k.val + 2)),
          |u (diagAxisGen M ha k i)| ^ (2 * ((Text M (tach M) (k.val + 2) : ℕ) - 1 - (i : ℕ))) := by
  rw [kLDU_ambient_abs_det M (tach M) ha]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hpiv : (matrixSplit (Matrix.of (readK M (tach M) ha
        (pivotBlowupOn (activeMGen M ha) p₀ u) k))).2.1 i
      = u (diagAxisGen M ha k i) := by
    rw [u_diagAxisGen M ha u k i]
    exact readK_pbo_allGen_at M ha p₀ hp₀ u k i i
  rw [hpiv]

/-- **`eDeepRank0_leafHGen` at a diagonal K-axis** — `= (r_k+c_k) + 2(t_k−1−i)` (the K-slot is `≠ p₀`,
so the `if j = p₀` is false; the `liveLeafHOnIdxGen` branch fires exactly as `leafHGen_diagAxisGen`). -/
theorem eDeepRank0_leafHGen_diagAxisGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (p₀ : Fin (routeMAmbient M)) (hp₀ : p₀ ∈ activeMGen M ha) (k : Fin L)
    (i : Fin (Text M (tach M) (k.val + 2))) :
    eDeepRank0_leafHGen M ha p₀ (diagAxisGen M ha k i)
      = (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
        + (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
        + 2 * (Text M (tach M) (k.val + 2) - 1 - (i : ℕ)) := by
  have hne : diagAxisGen M ha k i ≠ p₀ := by
    have hnm : diagAxisGen M ha k i ∉ activeMGen M ha := by
      rw [diagAxisGen]; exact readKslot_notMem_activeMGen M ha k i i
    exact fun h => hnm (h ▸ hp₀)
  rw [eDeepRank0_leafHGen, if_neg hne]
  rw [diagAxisGen, readKslot, Equiv.apply_symm_apply, liveLeafHOnIdxGen]
  simp only [Equiv.apply_symm_apply, finProdFinEquiv.symm_apply_apply]
  rfl

/-- **The off-image collapse for `eDeepRank0_leafHGen`** — a non-`p₀` axis with nonzero
`eDeepRank0_leafHGen` IS a diagonal K-axis. Mirrors `mem_image_diagAxisSigma_of_leafHGen_ne_zero`
(same `liveLeafHOnIdxGen` branch; the `p₀` singling replaces `leafPivot`). -/
theorem mem_image_diagAxisSigma_of_eDeepRank0leafHGen_ne_zero (M : Fin (L + 1) → ℕ)
    (ha : StructAdm M (tach M)) (p₀ : Fin (routeMAmbient M)) (j : Fin (routeMAmbient M))
    (hjp : j ≠ p₀) (hne : eDeepRank0_leafHGen M ha p₀ j ≠ 0) :
    j ∈ Finset.image (diagAxisSigmaGen M ha) Finset.univ := by
  rw [eDeepRank0_leafHGen, if_neg hjp] at hne
  have hjq : j = (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
      (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL j) := by
    rw [Equiv.symm_apply_apply]
  match hc : chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL j with
  | ⟨k, Sum.inr s⟩ => rw [hc] at hne; simp only [liveLeafHOnIdxGen] at hne; exact absurd rfl hne
  | ⟨k, Sum.inl s⟩ =>
    rw [hc] at hne; simp only [liveLeafHOnIdxGen] at hne
    match hfeq : frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s with
    | Sum.inl (Sum.inl (Sum.inl qK)) =>
      rw [hfeq] at hne; simp only at hne
      by_cases hdiag : (finProdFinEquiv.symm qK).1 = (finProdFinEquiv.symm qK).2
      · refine Finset.mem_image.mpr ⟨⟨k, (finProdFinEquiv.symm qK).1⟩, Finset.mem_univ _, ?_⟩
        have hs : s = (frameSplitEquiv M (tach M) (k.val + 1)
            (ha.hdesc k.val k.isLt) (ha.hub k.val)).symm
              (Sum.inl (Sum.inl (Sum.inl qK))) := by rw [← hfeq, Equiv.symm_apply_apply]
        have hqK : finProdFinEquiv ((finProdFinEquiv.symm qK).1, (finProdFinEquiv.symm qK).1) = qK := by
          nth_rewrite 2 [hdiag]
          rw [Prod.mk.eta, finProdFinEquiv.apply_symm_apply]
        rw [diagAxisSigmaGen, diagAxisGen, readKslot, hjq, hc, hs, hqK]
      · rw [if_neg hdiag] at hne; exact absurd rfl hne
    | Sum.inl (Sum.inl (Sum.inr e)) => rw [hfeq] at hne; simp only at hne; exact absurd rfl hne
    | Sum.inl (Sum.inr e) => rw [hfeq] at hne; simp only at hne; exact absurd rfl hne
    | Sum.inr e => rw [hfeq] at hne; simp only at hne; exact absurd rfl hne

/-- **The boundary-factor det monomializes (pivot-generic)** —
`|det D(BchartLeafGen ∘ kLDU)(pbo p₀ u)| = ∏_{j ≠ p₀} |u_j|^{eDeepRank0_leafHGen p₀ j}`. Pivot-generic
lift of `interiorLive_BdetMonomialGen` (K-diagonal product; the E-slot pivot `p₀` replaces `leafPivot`,
its `eDeepRank0_leafHGen` base being `0` — but the excluded slot in the product is `p₀`). -/
theorem interiorLive_BdetMonomialGen_at (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (p₀ : Fin (routeMAmbient M)) (hp₀ : p₀ ∈ activeMGen M ha) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (fun y => BchartLeafGen M ha (kLDU M (tach M) ha y))
        (pivotBlowupOn (activeMGen M ha) p₀ u)).toLinearMap|
      = ∏ j, if j = p₀ then (1 : ℝ)
          else |u j| ^ (eDeepRank0_leafHGen M ha p₀ j) := by
  rw [Dtot_kLDU_abs_det_split M ha, Dtot_factor1_pbo_at M ha p₀ hp₀ u,
    kLDU_ambient_det_pbo_gen_at M ha p₀ hp₀ u,
    lhs_collapse_multiboundary (fun s => Text M (tach M) (s.val + 2))
      (fun s => Text M (tach M) (s.val + 1) - Text M (tach M) (s.val + 2))
      (fun s => Wext M (s.val + 1) - Text M (tach M) (s.val + 2))
      (fun s => fun i => u (diagAxisGen M ha s i))]
  have hexp : ∀ (s : Fin L) (i : Fin (Text M (tach M) (s.val + 2))),
      |u (diagAxisGen M ha s i)|
        ^ (((Text M (tach M) (s.val + 1) - Text M (tach M) (s.val + 2))
              + (Wext M (s.val + 1) - Text M (tach M) (s.val + 2)))
          + 2 * ((Text M (tach M) (s.val + 2) : ℕ) - 1 - (i : ℕ)))
        = |u (diagAxisGen M ha s i)| ^ (eDeepRank0_leafHGen M ha p₀ (diagAxisGen M ha s i)) := by
    intro s i
    rw [eDeepRank0_leafHGen_diagAxisGen M ha p₀ hp₀ s i]
  rw [Finset.prod_congr rfl (fun s _ => Finset.prod_congr rfl (fun i _ => hexp s i))]
  let g : Fin (routeMAmbient M) → ℝ := fun j => |u j| ^ (eDeepRank0_leafHGen M ha p₀ j)
  show ∏ s : Fin L, ∏ i, g (diagAxisGen M ha s i) = ∏ j, if j = p₀ then (1 : ℝ) else g j
  rw [← Fintype.prod_sigma' (fun s i => g (diagAxisGen M ha s i))]
  have hRHS : (∏ j, if j = p₀ then (1 : ℝ) else g j)
      = ∏ j ∈ (Finset.univ : Finset (Fin (routeMAmbient M))).erase p₀, g j := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => if j = p₀ then (1 : ℝ) else g j)
      (Finset.mem_univ p₀), if_pos rfl, one_mul]
    exact Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))
  have hLHS : (∏ p : (Σ k : Fin L, Fin (Text M (tach M) (k.val + 2))), g (diagAxisGen M ha p.1 p.2))
      = ∏ j ∈ (Finset.univ : Finset (Fin (routeMAmbient M))).erase p₀, g j := by
    rw [show (∏ p : (Σ k : Fin L, Fin (Text M (tach M) (k.val + 2))), g (diagAxisGen M ha p.1 p.2))
        = ∏ p : (Σ k : Fin L, Fin (Text M (tach M) (k.val + 2))), g (diagAxisSigmaGen M ha p) from rfl]
    rw [← Finset.prod_image (g := diagAxisSigmaGen M ha) (f := g)
      ((diagAxisSigmaGen_injective M ha).injOn)]
    refine Finset.prod_subset ?_ ?_
    · intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨⟨k, i⟩, _, rfl⟩ := hj
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      have hnm : diagAxisSigmaGen M ha ⟨k, i⟩ ∉ activeMGen M ha := by
        rw [diagAxisSigmaGen, diagAxisGen]; exact readKslot_notMem_activeMGen M ha k i i
      exact fun h => hnm (h ▸ hp₀)
    · intro j hj hjimg
      have hjp : j ≠ p₀ := (Finset.mem_erase.mp hj).1
      have hz : eDeepRank0_leafHGen M ha p₀ j = 0 := by
        by_contra hne
        exact hjimg (mem_image_diagAxisSigma_of_eDeepRank0leafHGen_ne_zero M ha p₀ j hjp hne)
      show g j = 1
      simp only [g]; rw [hz, pow_zero]
  rw [hLHS, hRHS]

/-! ## The chart Jacobian abs-det headline + the map factorization -/

/-- **The map factorization** `eDeepRank0PhiGen = (fun y => BchartLeafGen (kLDU y)) ∘ pbo p₀` — from
`hmap_EfpGen` (at `kLDU x`) + the commute `kLDU_pbo_commuteGen_at`. -/
theorem eDeepRank0PhiGen_factor (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1) (hdr0 : Text M (tach M) L = 0)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2
      = (fun y => BchartLeafGen M ha (kLDU M (tach M) ha y))
        ∘ pivotBlowupOn (activeMGen M ha) (eBlockPivotGen M ha k hr hc) := by
  set p₀ := eBlockPivotGen M ha k hr hc with hp₀
  have hp₀mem : p₀ ∈ activeMGen M ha := eBlockPivotGen_mem_activeMGen M ha k hk hr hc
  funext x
  show phiEfpAt M ha k p₀ hp1 hp2 (kLDU M (tach M) ha x) = _
  rw [hmap_EfpGen M ha k hk hdr0 hr hc hp1 hp2]
  show BchartLeafGen M ha (pivotBlowupOn (activeMGen M ha) p₀ (kLDU M (tach M) ha x)) = _
  rw [kLDU_pbo_commuteGen_at M ha p₀ hp₀mem x]
  rfl

/-- **The chart Jacobian abs-det** — `|det D(eDeepRank0PhiGen) u| = ∏_j |u_j|^{eDeepRank0_leafHGen p₀ j}`.
The route-#1 radial split (`radialComp_abs_det_at` at `p₀ = eBlockPivotGen`) gives
`|u p₀|^{minAdm−1} · |det D(BchartLeafGen ∘ kLDU)(pbo u)|`, and the boundary factor monomializes
(`interiorLive_BdetMonomialGen_at`) to `∏_{j ≠ p₀} |u_j|^{leafHGen j}`; the radial fills the pivot
slot (`eDeepRank0_leafHGen_pivot`). -/
theorem eDeepRank0_abs_detGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1) (hdr0 : Text M (tach M) L = 0)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1))
    (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2) u).toLinearMap|
      = ∏ j, |u j| ^ (eDeepRank0_leafHGen M ha (eBlockPivotGen M ha k hr hc) j) := by
  set p₀ := eBlockPivotGen M ha k hr hc with hp₀
  have hp₀mem : p₀ ∈ activeMGen M ha := eBlockPivotGen_mem_activeMGen M ha k hk hr hc
  set B' := fun y => BchartLeafGen M ha (kLDU M (tach M) ha y) with hB'
  have hmap : eDeepRank0PhiGen M ha k p₀ hp1 hp2 = B' ∘ pivotBlowupOn (activeMGen M ha) p₀ :=
    eDeepRank0PhiGen_factor M ha k hk hdr0 hr hc hp1 hp2
  have hasDB' : HasFDerivAt B'
      (fderiv ℝ B' (pivotBlowupOn (activeMGen M ha) p₀ u))
      (pivotBlowupOn (activeMGen M ha) p₀ u) :=
    ((Bchart_differentiableAtGen M ha _).comp _
      (differentiable_kLDUGen M (tach M) ha _)).hasFDerivAt
  rw [radialComp_abs_det_at M (activeMGen M ha) p₀ hp₀mem
    (activeMGen_card M ha) B' (eDeepRank0PhiGen M ha k p₀ hp1 hp2) u _ hmap hasDB',
    interiorLive_BdetMonomialGen_at M ha p₀ hp₀mem u]
  conv_rhs => rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ p₀)
    (fun j => |u j| ^ (eDeepRank0_leafHGen M ha p₀ j))]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ p₀)
    (fun j => if j = p₀ then (1 : ℝ) else |u j| ^ (eDeepRank0_leafHGen M ha p₀ j))]
  rw [if_pos rfl, one_mul, eDeepRank0_leafHGen_pivot M ha p₀]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [if_neg (by simp at hj; exact hj : j ≠ p₀)]

/-- **`eDeepRank0PhiGen` is differentiable** — the factorization + each factor differentiable. -/
theorem eDeepRank0_diffGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val ≠ L - 1) (hdr0 : Text M (tach M) L = 0)
    (hr : 0 < Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
    (hc : 0 < Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    Differentiable ℝ (eDeepRank0PhiGen M ha k (eBlockPivotGen M ha k hr hc) hp1 hp2) := by
  rw [eDeepRank0PhiGen_factor M ha k hk hdr0 hr hc hp1 hp2]
  refine Differentiable.comp ?_ (differentiable_pivotBlowupOnGen (activeMGen M ha) _)
  exact fun y => ((fun u => Bchart_differentiableAtGen M ha u) _).comp y
    (differentiable_kLDUGen M (tach M) ha y)

end DLNFibre.DLN.RLCT
