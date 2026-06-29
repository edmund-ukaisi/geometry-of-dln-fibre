import DLNFibre.DLN.RLCT.Validate.DeepestL2Wiring
import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2Conj
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShiftConj
import DLNFibre.DLN.RLCT.Validate.DeepestLeadingBlock

/-! # Scratch: L2 leg-close pieces (route-b), verified before wiring into `deepest_gauge_construction`.

**Status (genm-l2fin).** This file now holds only the step-(c) `example` contracts (validation pins for
the wire). The conjugated `hsub3reg` apparatus that lived here — `deepestEFull_sq_sum_psiSplitRawL2CoreConj_eq_germ`
(the LINK-1 reg-energy germ), `conj_he2_raw`, `conj_hm_triple`, `e2_conj_dict`, and the `reindex_decode*`
helpers — is CLOSED, sorry-free + axiom-clean `[propext, Classical.choice, Quot.sound]`, and has been
PROMOTED to the public leaf module `DeepestL2ConjReg.lean` so the wire (`DeepestL2Wiring`) can import it.

**Step (c) examples (below).** `example` contracts pinning the exact signatures the wire consumes (local
`have`s in `deepest_gauge_construction`'s L=2 branch):
- `hDA-0`   : `IsUnit (deepBlkA 0)` — `deepestPoint_leadingBlock_isUnit` + inline submatrix↔toBlocks₁₁
              (`rThresholdSplit_symm_inl`).
- `hDA-last`: `IsUnit (deepBlkA last)` — corner identity `(reindex(dP·Qf))₁₁ = 1` + `Qf₂₁ = 0`
              (`reindex_mul_fromBlocks`) ⟹ `deepBlkA_last · M = 1` ⟹ det unit; column equiv collapsed
              by `pivotThresholdSplit_pivotJSucc_frontEmbed`.
- `hDA ∀ s` : the two layers assembled at `L = 2`.
- `hY`/`hZ` : `deepBlkY_layer0_zero` / `deepBlkZ_layerLast_zero`.
- `hbdy`    : `deepBlk_boundary_of_L2`.
- conj spectator: `(conjAbsorb q).2.2 = q.2.2` via `coreShearHomeo_spectator`.
- `psiSplitRawL2CoreConj` continuous-at-0 (for the `hsub4core` closedBall germ). -/

open MeasureTheory Topology Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

-- Step (c) pieces: hY, hZ, hbdy come directly from banked lemmas at L=2.
-- Layer-0 hDA: IsUnit (deepBlkA 0) from deepestPoint_leadingBlock_isUnit + inline submatrix↔toBlocks₁₁.

/-- Layer-0 conjugated pivot base is a unit: `deepBlkA 0` IS the leading r×r block, a unit by htop. -/
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r) :
    IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)) := by
  have hlead := deepestPoint_leadingBlock_isUnit H r B hB hr hL hL2 htop
  -- deepBlkA 0 = (reindex rThr rThr (deepestPoint 0)).toBlocks₁₁; show it equals the submatrix.
  have heq : deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)
      = (deepestPoint H r B hB hr hL (⟨0, by omega⟩ : Fin L)).submatrix
        (Fin.castLE (hr (⟨0, by omega⟩ : Fin L).castSucc) : Fin r → Fin (H (⟨0, by omega⟩ : Fin L).castSucc))
        (Fin.castLE (hr (⟨0, by omega⟩ : Fin L).succ) : Fin r → Fin (H (⟨0, by omega⟩ : Fin L).succ)) := by
    apply Matrix.ext
    intro i j
    show (Matrix.reindex (rThresholdSplit r (H (⟨0, by omega⟩ : Fin L).castSucc) (hr _))
        (rThresholdSplit r (H (⟨0, by omega⟩ : Fin L).succ) (hr _))
        (deepestPoint H r B hB hr hL (⟨0, by omega⟩ : Fin L))).toBlocks₁₁ i j = _
    simp only [Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      rThresholdSplit_symm_inl]
  rw [heq]; exact hlead

-- hY at L=2: deepBlkY 0 = 0
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0 :=
  deepBlkY_layer0_zero H r B hB hr hL (by omega) (⟨0, by omega⟩ : Fin L) rfl

-- hZ at L=2: deepBlkZ last = 0
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    deepBlkZ H r B hB hr hL (lastLayer hL) = 0 :=
  deepBlkZ_layerLast_zero H r B hB hr hL (by omega) (lastLayer hL)
    (by simp only [lastLayer]; omega)

-- hbdy: the boundary structure (both layers boundary at L=2)
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0 :=
  deepBlk_boundary_of_L2 H r B hB hr hL hL2eq

-- conj spectator: (conjAbsorb q).2.2 = q.2.2 via coreShearHomeo_spectator
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (q : DeepestSplit H r (deepestNGauge H r)) :
    (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.2 = q.2.2 :=
  coreShearHomeo_spectator (schurCutoffShiftConj H r B hB hr hL hDA)
    (continuous_schurCutoffShiftConj H r B hB hr hL hDA) q

/-! ### Step (e) germs: psiSplitRawL2CoreConj continuous-at-0 ⟹ closedBall germ; l2WConj.det germ. -/

-- psiSplitRawL2CoreConj continuous at the split origin (δc strict-deriv at 0 + id).
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0) :
    ContinuousAt (psiSplitRawL2CoreConj H r B hB hr hL hL2eq)
      (0 : DeepestSplit H r (deepestNGauge H r)) := by
  have hδ : ContinuousAt (fun q => psiSplitRawL2CoreConj H r B hB hr hL hL2eq q - q)
      (0 : DeepestSplit H r (deepestNGauge H r)) :=
    (hasStrictFDerivAt_psiSplitDeltaL2CoreConj_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ).continuousAt
  have hid : psiSplitRawL2CoreConj H r B hB hr hL hL2eq
      = fun q => (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q - q) + q := by
    funext q; rw [sub_add_cancel]
  rw [hid]; exact hδ.add continuousAt_id

/-! ### Step (c) last-layer hDA: IsUnit (deepBlkA last) via the corner identity + Qf block-upper. -/

-- Probe: deepBlkA last in terms of the pivotJSucc-split reindex, under hJfront.
-- Target: A₁₁·B₁₁ = 1 (from corner, Qf₂₁=0) ⟹ deepBlkA last is a unit.
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront' : J = frontEmbed H r hr)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    -- bundle corner (with pivotJSucc J), bundle hQUpper (Qf₂₁=0), aligned to pivotJSucc J:
    (hcorner : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hQUpper : (Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₁ = 0) :
    IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)) := by
  -- The shared middle split eMid := pivotThr (pivotJSucc J) on H ((lastLayer).succ).
  set eR := rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc) with heR
  set eMid := pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J) with heMid
  -- Block-mult: (reindex eR eMid (dP * Qf))₁₁ = A₁₁·B₁₁ + A₁₂·B₂₁.
  have hblk := reindex_mul_fromBlocks eR eMid eMid
    (deepestPoint H r B hB hr hL (lastLayer hL)) (Qf (lastLayer hL))
  -- corner ₁₁ = 1.
  have hc11 : (Matrix.reindex eR eMid
      ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))).toBlocks₁₁
      = (1 : Matrix (Fin r) (Fin r) ℝ) := by
    rw [show Matrix.reindex eR eMid
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 from hcorner,
      Matrix.toBlocks_fromBlocks₁₁]
  -- A₁₁·B₁₁ = 1 (Qf₂₁ = 0 kills the second summand).
  have hkey : (Matrix.reindex eR eMid (deepestPoint H r B hB hr hL (lastLayer hL))).toBlocks₁₁
      * (Matrix.reindex eMid eMid (Qf (lastLayer hL))).toBlocks₁₁ = 1 := by
    have h := hc11
    rw [hblk, Matrix.toBlocks_fromBlocks₁₁, hQUpper, Matrix.mul_zero, add_zero] at h
    exact h
  -- A₁₁ = deepBlkA last (the pivotJSucc-split column equiv collapses to rThr under hJfront).
  have hAeq : (Matrix.reindex eR eMid (deepestPoint H r B hB hr hL (lastLayer hL))).toBlocks₁₁
      = deepBlkA H r B hB hr hL (lastLayer hL) := by
    have hpiv : eMid = rThresholdSplit r (H ((lastLayer hL).succ)) (hr ((lastLayer hL).succ)) := by
      rw [heMid, hJfront', pivotThresholdSplit_pivotJSucc_frontEmbed H r hr hL]
    rw [hpiv]; rfl
  rw [hAeq] at hkey
  -- A·B = 1 (square matrices) ⟹ det A · det B = 1 ⟹ det A is a unit ⟹ A is a unit.
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet : (deepBlkA H r B hB hr hL (lastLayer hL)).det
      * (Matrix.reindex eMid eMid (Qf (lastLayer hL))).toBlocks₁₁.det = 1 := by
    rw [← Matrix.det_mul, hkey, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ hdet

/-! ### hDA assembly: ∀ s : Fin L at L=2 from the two layers. -/

-- At L=2, ∀ s : Fin L reduces to s=0 and s=lastLayer; assemble from the two banked units.
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDAlast : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL))) :
    ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s) := by
  intro s
  rcases Nat.eq_zero_or_pos (s : ℕ) with hs0 | hspos
  · have : s = (⟨0, by omega⟩ : Fin L) := Fin.ext hs0
    rw [this]; exact hDA0
  · have : s = lastLayer hL := by
      apply Fin.ext; simp only [lastLayer]
      have := s.isLt; omega
    rw [this]; exact hDAlast

/-! ### The conjugated `hm11/hm12/hm21` (the long pole) — Codex-mapped route.

Build the three block agreements for `prod H Aψ` vs `prod H Aq` where `Aq = decode x`,
`Aψ = decode (split.symm (psiSplitRawL2CoreConj (split x)))`, then `hsub3reg` = #147 verbatim. -/

-- Per-layer block dictionary at the MOVED point (reindex(Aψ s)₁₁) via the chart-point readback +
-- the conj gaugeReadX-transport + the split round-trip. Layer s, boundary (deepBlkT_s = 0).
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (x : Fin (flatDim H) → ℝ) (s : Fin L)
    (hT : (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₂₂ = 0) :
    (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ))
        (((paramsEquivFlat H).symm (split.symm
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)))) s)).toBlocks₁₁
      = deepBlkA H r B hB hr hL s
        + gaugeReadX H r hr hL ((split x).1, (split x).2.2) s := by
  set w := split.symm (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)) with hw
  have hrt : deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w
      = psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x) := by
    rw [← hsplit w, hw, split.apply_symm_apply]
  obtain ⟨h11, _, _, _⟩ := reindex_decode_split_toBlocks H r B hB hr hL w s hT
  rw [h11, hrt, gaugeReadX_psiSplitRawL2CoreConj_eq]

end DLNFibre.DLN.RLCT
