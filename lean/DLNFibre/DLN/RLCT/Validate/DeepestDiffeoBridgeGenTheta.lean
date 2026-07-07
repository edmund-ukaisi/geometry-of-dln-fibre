import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShiftConj

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeGenTheta` — the general-`L` Step Θ (naive↔conj MP bridge)

The general-`L` lift of the L=2 LINK-2 (`DeepestL2ConjSub4`'s `link2_at_zero_gaugeReg` /
`link2_at_wstar_gaugeReg`): the naive↔conjugate core-absorb RLCT bridge, the Θ half of the two-step
`hstep2 = Step Θ ∘ Step Ψ_conj` (the accepted L=2 template `deepest_diffeo_bridge_L2_assembled`).

## What Step Θ is (chain-free)
`Φconj = ∑ (regStraighten (split x))² + deepestCoreF (deepestCoreAbsorbConj (split x)).2.1` and
`Φnaive = ∑ (regStraighten (split x))² + deepestCoreF (deepestCoreAbsorb (split x)).2.1` have the SAME
local RLCT at `wstar`. The L=2 route (mirrored here):
* straighten the `deepestEFull` reg output down to the GAUGE reg `∑ q.1²` (which `thetaConj` fixes,
  since `thetaConj` fixes `q.1`) — `regAbsorb_bare` / `regAbsorb_conj`;
* at gauge reg, the BANKED general `rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb` (the MP core-shear `Θ`,
  det-1, basepoint-and-reg-fixing) peels bare↔conj with NO derivative bookkeeping;
* transport gauge-`0` ↔ chart-`wstar` by the MP homeomorphism `split` (`rlctAtOn_comp_homeomorph`).

## What LANDS here (fully general-`L`, sorry-free)
* `deepestEFull_bare_hTilde_exists_gen` — the BARE reg-absorb π̃ local-diffeo data. The bare absorb's
  shift derivative VANISHES (`hasStrictFDerivAt_schurCutoffShift_zero`), so `D(coreAbsorb.symm)(0) = id`
  and `eTilde = e` from the general `deepestEFull_deriv`. (The general lift of the `Fin 3`
  `deepestEFull_bare_hTilde_exists`; its body used only general lemmas.)
* `regAbsorbPeel_bare_gen`, `regAbsorb_bare_gen` — the general bare reg-absorb (straighten
  `deepestEFull` reg to gauge reg), via `rlctAtOn_comp_localDiffeo` + `rlctAtOn_regAbsorb_reduce2`.
* `link2_at_zero_gaugeReg_gen` — the gauge-`0` Step Θ, discharging bare (built) + the banked Θ-peel,
  taking the CONJ reg-absorb `regAbsorb_conj` as the single hypothesis `hRegAbsorbConj`.
* `link2_at_wstar_gaugeReg_gen` — the chart-`wstar` Step Θ (split transport).

## The single remaining Step-Θ piece (the CONJ reg-absorb, threaded as `hRegAbsorbConj`)
The conjugate absorb `deepestCoreAbsorbConj` has a NONZERO shift derivative (the "value-fold atom"), so
`D(conjAbsorb.symm)(0) ≠ id`; the conj π̃'s reg-reg block stays invertible only via
`∂deepestEFull/∂core(0) = 0` (the general lift of the `Fin 3` `deepestEFull_coreConstant` — LABOR,
not a wall: it is the deepest-point corner factorization
`prod(framed)|_{reg=0} = fromBlocks 1 0 0 junk`, core-independent in its `{11,12,21}` blocks). Until
that general atom lands, the conj reg-absorb enters as `hRegAbsorbConj`. (LINK-1, Step Ψ_conj — the
honest chain `Ĉ` + `psiSplitRawL2CoreConj` general — is the separate coupled bulk, not touched here.)
-/

open MeasureTheory Topology Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The general-`L` BARE `hTilde`** — the bare reg-absorb peel's local-diffeo data (the `Fin 3`
`deepestEFull_bare_hTilde_exists` lifted to general `L`). The bare core absorb `deepestCoreAbsorb`
has a VANISHING shift derivative (`hasStrictFDerivAt_schurCutoffShift_zero`), so `D(coreAbsorb.symm)(0) = id`
and `eTilde = e` from the general `deepestEFull_deriv` directly. -/
theorem deepestEFull_bare_hTilde_exists_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂)) :
    ∃ eTilde : DeepestSplit H r (deepestNGauge H r) ≃L[ℝ] DeepestSplit H r (deepestNGauge H r),
      ContDiff ℝ (⊤ : ℕ∞)
        (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf
          ((deepestCoreAbsorb H r hr hL).symm q))) ∧
      HasStrictFDerivAt (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf
          ((deepestCoreAbsorb H r hr hL).symm q)))
        (eTilde : DeepestSplit H r (deepestNGauge H r) →L[ℝ]
          DeepestSplit H r (deepestNGauge H r)) 0 := by
  set coreAbsorb := deepestCoreAbsorb H r hr hL with hca_def
  obtain ⟨D_E, e, hsd, he⟩ :=
    deepestEFull_deriv H r hr hL hL2 J Pf Qf hPf hQf hQf0 hPfL hQf22
  have hcds : ContDiff ℝ (⊤ : ℕ∞) (schurCutoffShift H r hr hL) :=
    contDiff_schurCutoffShift H r hr hL
  have hsymm_cd : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) => coreAbsorb.symm q) := by
    rw [hca_def, deepestCoreAbsorb]
    exact contDiff_coreShearHomeo_symm (schurCutoffShift H r hr hL)
      (continuous_schurCutoffShift H r hr hL) hcds
  have hsymm_sd : HasStrictFDerivAt
      (fun q : DeepestSplit H r (deepestNGauge H r) => coreAbsorb.symm q)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r))) 0 := by
    rw [hca_def, deepestCoreAbsorb]
    exact hasStrictFDerivAt_coreShearHomeo_symm_zero (schurCutoffShift H r hr hL)
      (continuous_schurCutoffShift H r hr hL) (hasStrictFDerivAt_schurCutoffShift_zero H r hr hL)
  set Ecomp : DeepestSplit H r (deepestNGauge H r) → (Fin (deepestNReg H r) → ℝ) :=
    fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q) with hEcomp
  have hEcomp_cd : ContDiff ℝ (⊤ : ℕ∞) Ecomp :=
    (deepestEFull_contdiff H r hr hL J Pf Qf).comp hsymm_cd
  have hcontdiff : ContDiff ℝ (⊤ : ℕ∞) (regStraightenOf2 Ecomp) :=
    contDiff_regStraightenOf2 Ecomp hEcomp_cd
  have hEcomp_sd : HasStrictFDerivAt Ecomp D_E 0 := by
    have hsymm0 : coreAbsorb.symm (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
      have hca_base : coreAbsorb 0 = 0 := by
        rw [hca_def]; exact (deepest_coreAbsorb_exists H r hr hL).1
      conv_lhs => rw [← hca_base]; rw [coreAbsorb.symm_apply_apply]
    have hsd' : HasStrictFDerivAt (deepestEFull H r hr hL J Pf Qf) D_E
        (coreAbsorb.symm (0 : DeepestSplit H r (deepestNGauge H r))) := by
      rw [hsymm0]; exact hsd
    have hchain := hsd'.comp (x := (0 : DeepestSplit H r (deepestNGauge H r))) hsymm_sd
    have hchain' : HasStrictFDerivAt Ecomp (D_E.comp
        (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r)))) 0 := hchain
    rw [ContinuousLinearMap.comp_id] at hchain'
    exact hchain'
  have hreg_sd := hasStrictFDerivAt_regStraightenOf2_gen Ecomp D_E hEcomp_sd
  refine ⟨e, hcontdiff, ?_⟩
  rw [he]
  exact hreg_sd

/-- **The general-`L` π̃ reg-absorb peel, BARE side** (the `Fin 3` `regAbsorbPeel_bare` lifted). The bare
π̃ `q ↦ (deepestEFull (coreAbsorb.symm q), q.2)` is a local diffeo at `0` (`deepestEFull_bare_hTilde_exists_gen`);
`rlctAtOn_comp_localDiffeo` peels it, straightening `deepestEFull ∘ coreAbsorb.symm` to the gauge reg `∑ q.1²`. -/
theorem regAbsorbPeel_bare_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂)) :
    rlctAtOn
        (fun q : DeepestSplit H r (deepestNGauge H r) =>
          (∑ i, deepestEFull H r hr hL J Pf Qf
            ((deepestCoreAbsorb H r hr hL).symm q) i ^ 2)
          + deepestCoreF H r q.2.1)
        (0 : DeepestSplit H r (deepestNGauge H r))
      = rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
          (0 : DeepestSplit H r (deepestNGauge H r)) := by
  set coreAbsorb := deepestCoreAbsorb H r hr hL with hca_def
  obtain ⟨eTilde, hTilde_contdiff, hTilde_deriv⟩ :=
    deepestEFull_bare_hTilde_exists_gen H r hr hL hL2 J Pf Qf hPf hQf hQf0 hPfL hQf22
  have hsymm0 : coreAbsorb.symm (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
    have hca_base : coreAbsorb 0 = 0 := by
      rw [hca_def]; exact (deepest_coreAbsorb_exists H r hr hL).1
    conv_lhs => rw [← hca_base]; rw [coreAbsorb.symm_apply_apply]
  have hkey := rlctAtOn_comp_localDiffeo
    (fun q : DeepestSplit H r (deepestNGauge H r) => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
    (0 : DeepestSplit H r (deepestNGauge H r))
    (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)))
    eTilde hTilde_contdiff hTilde_deriv
    (regStraightenOf2_basepoint (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) (by
      change deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm 0) = 0
      rw [hsymm0]; exact deepestEFull_base H r hr hL hL2 J Pf Qf))
  have hfun : (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (∑ i, (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) q).1 i ^ 2)
          + deepestCoreF H r
            (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) q).2.1)
      = fun q : DeepestSplit H r (deepestNGauge H r) =>
        (∑ i, deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q) i ^ 2) + deepestCoreF H r q.2.1 := by
    funext q; rfl
  rw [hfun] at hkey
  exact hkey

/-- **The general-`L` gauge-reg reg-absorb (BARE)**, via `rlctAtOn_regAbsorb_reduce2` +
`regAbsorbPeel_bare_gen`: straightens the `deepestEFull` reg output down to the gauge reg `∑ q.1²`,
holding the BARE core absorb fixed. -/
theorem regAbsorb_bare_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂)) :
    rlctAtOn
        (fun q : DeepestSplit H r (deepestNGauge H r) =>
          (∑ i, deepestEFull H r hr hL J Pf Qf q i ^ 2)
          + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1)
        (0 : DeepestSplit H r (deepestNGauge H r))
      = rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, q.1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r)) :=
  rlctAtOn_regAbsorb_reduce2 (deepestCoreAbsorb H r hr hL)
    (deepestEFull H r hr hL J Pf Qf) (fun rr => ∑ i, rr i ^ 2) (deepestCoreF H r)
    (deepestCoreAbsorb_mp H r hr hL)
    ((deepest_coreAbsorb_exists H r hr hL).1)
    ((deepest_coreAbsorb_exists H r hr hL).2.1)
    (regAbsorbPeel_bare_gen H r hr hL hL2 J Pf Qf hPf hQf hQf0 hPfL hQf22)

/-- **The general-`L` LINK-2 at gauge `0` — Step Θ (naive↔conj), gauge-reg sandwich.** With
`regStraighten.1 = deepestEFull` (`hregval`): `conj-target =[hRegAbsorbConj] gauge-reg+conjAbsorb
=[rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb, banked general] gauge-reg+bareAbsorb =[regAbsorb_bare_gen⁻¹]
bare-target`. The BARE reg-absorb + the Θ-peel are DISCHARGED here (both general); the CONJ reg-absorb
enters as `hRegAbsorbConj` (rides the general value-fold atom, not yet landed). -/
theorem link2_at_zero_gaugeReg_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hregval : ∀ q, (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q)
    (hRegAbsorbConj :
      rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, deepestEFull H r hr hL J Pf Qf q i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r))
        = rlctAtOn
            (fun q : DeepestSplit H r (deepestNGauge H r) =>
              (∑ i, q.1 i ^ 2)
                + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
            (0 : DeepestSplit H r (deepestNGauge H r))) :
    rlctAtOn
        (fun q : DeepestSplit H r (deepestNGauge H r) =>
          (∑ i, (regStraighten q).1 i ^ 2)
            + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
        (0 : DeepestSplit H r (deepestNGauge H r))
      = rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, (regStraighten q).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r)) := by
  simp only [hregval]
  rw [hRegAbsorbConj,
    ← rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb H r B hB hr hL hDA hbdy,
    ← regAbsorb_bare_gen H r hr hL hL2 J Pf Qf hPf hQf hQf0 hPfL hQf22]

/-- **The general-`L` LINK-2 at flat `wstar` — Step Θ (chart frame).** The gauge-`0` form
`link2_at_zero_gaugeReg_gen` transported along the MP homeomorphism `split` (`rlctAtOn_comp_homeomorph`,
`split wstar = 0`). Closes the Θ half of `hstep2 = Step Θ ∘ Step Ψ_conj` at general `L`, modulo the
conj reg-absorb `hRegAbsorbConj`. -/
theorem link2_at_wstar_gaugeReg_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hregval : ∀ q, (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q)
    (hRegAbsorbConj :
      rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, deepestEFull H r hr hL J Pf Qf q i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r))
        = rlctAtOn
            (fun q : DeepestSplit H r (deepestNGauge H r) =>
              (∑ i, q.1 i ^ 2)
                + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
            (0 : DeepestSplit H r (deepestNGauge H r)))
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit_mp : MeasurePreserving split volume volume)
    (wstar : Fin (flatDim H) → ℝ)
    (hsplit_wstar : split wstar = (0 : DeepestSplit H r (deepestNGauge H r))) :
    rlctAtOn
        (fun x : Fin (flatDim H) → ℝ =>
          (∑ i, (regStraighten (split x)).1 i ^ 2)
            + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA (split x)).2.1)
        wstar
      = rlctAtOn
          (fun x : Fin (flatDim H) → ℝ =>
            (∑ i, (regStraighten (split x)).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorb H r hr hL (split x)).2.1)
          wstar := by
  have hconj := rlctAtOn_comp_homeomorph split hsplit_mp split.measurableEmbedding
    (fun q : DeepestSplit H r (deepestNGauge H r) =>
      (∑ i, (regStraighten q).1 i ^ 2)
        + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1) wstar
  have hbare := rlctAtOn_comp_homeomorph split hsplit_mp split.measurableEmbedding
    (fun q : DeepestSplit H r (deepestNGauge H r) =>
      (∑ i, (regStraighten q).1 i ^ 2)
        + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1) wstar
  rw [hsplit_wstar] at hconj hbare
  rw [hconj, hbare]
  exact link2_at_zero_gaugeReg_gen H r B hB hr hL hL2 hDA hbdy J Pf Qf hPf hQf hQf0 hPfL hQf22
    regStraighten hregval hRegAbsorbConj

end DLNFibre.DLN.RLCT
