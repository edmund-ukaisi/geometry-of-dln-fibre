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

/-! ## The deepRank = 0 chart + rate -/

/-- **The deepRank = 0 chart** at pivot boundary `k`, radial slot `p₀`:
`phiGen (x p₀) M tach (genBlkFlatEfpGen k x)`. General-`L` lift of `eDeepRank0Phi`. -/
noncomputable def eDeepRank0PhiGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) :=
  fun x => phiGen (x p₀) M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 x) (hleStruct M (tach M) ha)

/-- **The deepRank = 0 unit factor** `eDeepRank0UnitGen x := VvalGen (x p₀) … (genBlkFlatEfpGen k x)`. -/
noncomputable def eDeepRank0UnitGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (p₀ : Fin (routeMAmbient M))
    (hp1 : Text M (tach M) (k.val + 1 + 1) ≤ Text M (tach M) (k.val + 1))
    (hp2 : Text M (tach M) (k.val + 1 + 1) ≤ Wext M (k.val + 1)) :
    (Fin (routeMAmbient M) → ℝ) → ℝ :=
  fun x => VvalGen (x p₀) M (tach M) (genBlkFlatEfpGen M ha k hp1 hp2 x) (hleStruct M (tach M) ha)

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

end DLNFibre.DLN.RLCT
