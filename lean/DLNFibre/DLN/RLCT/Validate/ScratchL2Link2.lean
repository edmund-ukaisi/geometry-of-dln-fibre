import DLNFibre.DLN.RLCT.Validate.DeepestL2Wiring
import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2Conj
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShiftConj
import DLNFibre.DLN.RLCT.Validate.DeepestL2ConjSmooth

/-! # Scratch: LINK-2 (route-b close, the bare↔conj core RLCT bridge) — the Θ-peel half (banked) + the
sharpened single-ρ residual.

**`LINK2`** is the second half of `hstep2 = LINK1 ∘ LINK2`. `LINK1` (`deepest_diffeo_bridge_L2_conj_impl`,
sorry-free) gives `rlctAtOn Φscore wstar = rlctAtOn (R'∘split + coreF∘CONJabsorb∘split) wstar`; the
`deepest_gauge_construction` goal needs `… = rlctAtOn (R'∘split + coreF∘BAREabsorb∘split) wstar` (route-b
keeps `coreAbsorb` bare). So `LINK2 : rlctAtOn (R'∘split + coreF∘conjAbsorb∘split) wstar
= rlctAtOn (R'∘split + coreF∘bareAbsorb∘split) wstar`, with `R' = regStraighten·`.

**The Θ-peel HALF — `link2_thetaPeel_half` (BANKED, sorry-free).** Applying `rlctAtOn_comp_homeomorph Θ`
(`Θ = thetaConj`, MP det-1 core-shear, `Θ 0 = 0` from the boundary-vanishing `hbdy`) to the whole sum,
plus `bareAbsorb ∘ Θ = conjAbsorb` (`bareAbsorb_thetaConj_eq_conjAbsorb`):
`rlctAtOn (∑(regStraighten (Θ q)).1² + coreF∘conjAbsorb q) 0 = rlctAtOn (∑(regStraighten q).1² + coreF∘bareAbsorb q) 0`.
The RHS is the bare LINK2 target (post-split, at `0`). So the bare side is DISCHARGED.

**LINK2 CLOSES via the GAUGE-REG Θ-PEEL SANDWICH (`link2_at_zero_gaugeReg`, sorry-free).** Two earlier
routes died: (i) the single-bridge "option (b)" (`coreF(bareAbsorb(ψq))=coreF(conjAbsorb(q))` — FALSE,
exact witness); (ii) the comparability route `rlctAtOn_squeeze` on `∑R'(Θq)²+C` vs `∑R'(q)²+C` — also FALSE
(`F`,`Φ` have DIFFERENT zero sets, exact-rational witnesses W1/W2/W3, `codex_fix_witnesses.py`). The LIVE
route drops the reg from the core-reading `deepestEFull` level (where `Θ` drags) to the GAUGE reg `∑q.1²`
(where `Θ` FIXES `q.1`), applies the BANKED Θ-peel `rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb`
(`DeepestSchurShiftConj:439`, no drag), and lifts back via the `rlctAtOn_regAbsorb_reduce2` (π̃ option-D)
LOCAL-DIFFEO reg-absorb — which preserves zero sets, so the dead comparability does not recur. The two π̃
peels (`regAbsorbPeel_conj`/`_bare`) discharge via `rlctAtOn_comp_localDiffeo` + the `hTilde` local-diffeos
(`DeepestL2ConjSmooth.deepestEFull_{conj,bare}_hTilde_exists`): π̃ ContDiff⊤ (conj via the conj-smooth stack
`contDiff_schurCutoffShiftConj`, under `hDA`) + strict-deriv `= e` (an `≃L`, because the value-fold atom
`deepestEFull_coreConstant` annihilates the core-shear's reg→core mixing, keeping the reg block PIN-1's
invertible `F = I₃` — a44dd7e4 + Codex certified). All sorry-free, axiom-clean `[propext, Classical.choice,
Quot.sound]`.

(The DEAD comparability route — `rho_residual_epsBound`/`link2_rho_residual`/`link2_at_zero` — was REMOVED;
see the refutation note above the removed block below.) -/

open MeasureTheory Topology Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The Θ-peel half of LINK-2 (BANKED, sorry-free).** Peeling the MP det-1 core-shear `Θ = thetaConj`
off the WHOLE sum (`rlctAtOn_comp_homeomorph` + `bareAbsorb_thetaConj_eq_conjAbsorb`): the bare absorbed-core
RLCT equals the conjugated one with the reg argument pre-composed by `Θ`. Discharges the bare side of LINK-2;
the residual is the single reg-argument swap `Θ q ↦ q` (the `ρ`-residual). -/
theorem link2_thetaPeel_half (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r)) :
    rlctAtOn
        (fun q : DeepestSplit H r (deepestNGauge H r) =>
          (∑ i, (regStraighten (thetaConj H r B hB hr hL hDA q)).1 i ^ 2)
            + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
        (0 : DeepestSplit H r (deepestNGauge H r))
      = rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, (regStraighten q).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r)) := by
  set Θ := thetaConj H r B hB hr hL hDA with hΘ
  have hΘmp : MeasurePreserving Θ volume volume := by
    rw [hΘ, thetaConj]
    exact measurePreserving_coreShear (deepestNReg H r) (flatDim (deepestM H r)) (deepestNGauge H r)
      (shiftDiffConj H r B hB hr hL hDA) (continuous_shiftDiffConj H r B hB hr hL hDA)
  have hΘ0 : Θ 0 = 0 := by
    rw [hΘ, thetaConj]
    refine coreShearHomeo_basepoint (shiftDiffConj H r B hB hr hL hDA)
      (continuous_shiftDiffConj H r B hB hr hL hDA) ?_
    show shiftDiffConj H r B hB hr hL hDA (0, 0) = 0
    rw [shiftDiffConj,
      show ((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))
        = (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) from rfl,
      schurCutoffShiftConj_zero H r B hB hr hL hDA hbdy, schurCutoffShift_zero H r hr hL, sub_zero]
  have hkey := rlctAtOn_comp_homeomorph Θ hΘmp Θ.measurableEmbedding
    (fun q : DeepestSplit H r (deepestNGauge H r) =>
      (∑ i, (regStraighten q).1 i ^ 2)
        + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1) 0
  rw [hΘ0] at hkey
  rw [← hkey]
  congr 1
  funext q
  rw [bareAbsorb_thetaConj_eq_conjAbsorb H r B hB hr hL hDA q]

/-! ### The LIVE route — the gauge-reg Θ-peel sandwich (LANDED, `L = 2`).

(The DEAD comparability route — `rho_residual_epsBound` / `link2_rho_residual` / `link2_at_zero`,
REFUTED 2026-06-29: `F = ∑R'(Θq)²+C` and `Φ = ∑R'(q)²+C` have DIFFERENT zero sets, exact-rational
witnesses a44dd7e4 — has been REMOVED. It carried a `sorry` for an UNBUILDABLE bound and is fully
superseded by the gauge-reg sandwich below, which closes sorry-free.)

LINK2 (conj→bare core, at `0 : DeepestSplit`,
`regStraighten` reg term) closes by dropping to the GAUGE reg `∑q.1²` — where the BANKED Θ-peel
`rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb` (@439) converts bare↔conj with NO drag (`Θ` fixes `q.1`) — and
lifting back via the `rlctAtOn_regAbsorb_reduce2` (π̃ option-D) LOCAL-DIFFEO reg-absorb (which preserves zero
sets, so the dead comparability does not recur). The two `hpeel` residuals discharge via
`rlctAtOn_comp_localDiffeo` + the `DeepestL2ConjSmooth` `hTilde` lemmas (the conj one rides the value-fold
atom `deepestEFull_coreConstant`; the bare one is the wire's `hTilde` strict-deriv). `L = 2` (`Fin 3`),
the `deepestEFull_coreConstant` atom's scope. -/

/-- **π̃ reg-absorb peel, CONJ side (LANDED).** The `hpeel` input `rlctAtOn_regAbsorb_reduce2` needs for
`coreAbsorb := conjAbsorb`, `E := deepestEFull`: the conjugated π̃ `q ↦ (deepestEFull (conjAbsorb.symm q),
q.2)` is a local diffeo at `0`. Supplied by `deepestEFull_conj_hTilde_exists` (its invertible strict-deriv
rides the value-fold atom: the conj shift's nonzero `Dδ` moves only the core slot, which `D(deepestEFull)(0)`
annihilates), then `rlctAtOn_comp_localDiffeo` peels it. The conj analogue of the wire's bare `hTilde`. -/
theorem regAbsorbPeel_conj (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (hDA : ∀ s : Fin 2, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin 2, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0) :
    rlctAtOn
        (fun q : DeepestSplit H r (deepestNGauge H r) =>
          (∑ i, deepestEFull H r hr hL J Pf Qf
            ((deepestCoreAbsorbConj H r B hB hr hL hDA).symm q) i ^ 2)
          + deepestCoreF H r q.2.1)
        (0 : DeepestSplit H r (deepestNGauge H r))
      = rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
          (0 : DeepestSplit H r (deepestNGauge H r)) := by
  set coreAbsorb := deepestCoreAbsorbConj H r B hB hr hL hDA with hca_def
  obtain ⟨eTilde, hTilde_contdiff, hTilde_deriv⟩ :=
    deepestEFull_conj_hTilde_exists H r B hB hr hL hDA hbdy J hJfront Pf Qf hPf hQf hQf0 hPfL hQf22
      hPtri hQtri
  have hsymm0 : coreAbsorb.symm (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
    have hca_base : coreAbsorb 0 = 0 := by
      rw [hca_def]; exact deepestCoreAbsorbConj_basepoint H r B hB hr hL hDA hbdy
    conv_lhs => rw [← hca_base]; rw [coreAbsorb.symm_apply_apply]
  have hkey := rlctAtOn_comp_localDiffeo
    (fun q : DeepestSplit H r (deepestNGauge H r) => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
    (0 : DeepestSplit H r (deepestNGauge H r))
    (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)))
    eTilde hTilde_contdiff hTilde_deriv
    (regStraightenOf2_basepoint (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) (by
      show deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm 0) = 0
      rw [hsymm0]; exact deepestEFull_base H r hr hL (le_refl 2) J Pf Qf))
  have hfun : (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (∑ i, (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) q).1 i ^ 2)
          + deepestCoreF H r
            (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) q).2.1)
      = fun q : DeepestSplit H r (deepestNGauge H r) =>
        (∑ i, deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q) i ^ 2) + deepestCoreF H r q.2.1 := by
    funext q; rfl
  rw [hfun] at hkey
  exact hkey

/-- **π̃ reg-absorb peel, BARE side (LANDED).** The bare analogue of `regAbsorbPeel_conj`
(`coreAbsorb := deepestCoreAbsorb`); the bare π̃'s local-diffeo data is `deepestEFull_bare_hTilde_exists`
(`D(coreAbsorb.symm)(0) = id`, so `eTilde = e` directly). IS the wire's `hTilde` (DeepestL2Wiring:238). -/
theorem regAbsorbPeel_bare (H : Fin 3 → ℕ) (r : ℕ)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (J : Fin r ↪ Fin (H (Fin.last 2)))
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
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
    deepestEFull_bare_hTilde_exists H r hr hL J Pf Qf hPf hQf hQf0 hPfL hQf22
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
      show deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm 0) = 0
      rw [hsymm0]; exact deepestEFull_base H r hr hL (le_refl 2) J Pf Qf))
  have hfun : (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (∑ i, (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) q).1 i ^ 2)
          + deepestCoreF H r
            (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) q).2.1)
      = fun q : DeepestSplit H r (deepestNGauge H r) =>
        (∑ i, deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q) i ^ 2) + deepestCoreF H r q.2.1 := by
    funext q; rfl
  rw [hfun] at hkey
  exact hkey

/-- **The gauge-reg reg-absorb (CONJ), via `rlctAtOn_regAbsorb_reduce2` + `regAbsorbPeel_conj`.** Straightens
the `deepestEFull` reg output down to the gauge reg `∑q.1²`, holding the CONJ core absorb fixed. -/
theorem regAbsorb_conj (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (hDA : ∀ s : Fin 2, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin 2, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0) :
    rlctAtOn
        (fun q : DeepestSplit H r (deepestNGauge H r) =>
          (∑ i, deepestEFull H r hr hL J Pf Qf q i ^ 2)
          + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
        (0 : DeepestSplit H r (deepestNGauge H r))
      = rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, q.1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r)) :=
  rlctAtOn_regAbsorb_reduce2 (deepestCoreAbsorbConj H r B hB hr hL hDA)
    (deepestEFull H r hr hL J Pf Qf) (fun rr => ∑ i, rr i ^ 2) (deepestCoreF H r)
    (deepestCoreAbsorbConj_mp H r B hB hr hL hDA)
    (deepestCoreAbsorbConj_basepoint H r B hB hr hL hDA hbdy)
    (deepestCoreAbsorbConj_regular H r B hB hr hL hDA)
    (regAbsorbPeel_conj H r B hB hr hL hDA hbdy J hJfront Pf Qf hPf hQf hQf0 hPfL hQf22 hPtri hQtri)

/-- **The gauge-reg reg-absorb (BARE), via `rlctAtOn_regAbsorb_reduce2` + `regAbsorbPeel_bare`.** -/
theorem regAbsorb_bare (H : Fin 3 → ℕ) (r : ℕ)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (J : Fin r ↪ Fin (H (Fin.last 2)))
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
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
    (regAbsorbPeel_bare H r hr hL J Pf Qf hPf hQf hQf0 hPfL hQf22)

/-- **LINK-2 at `0` — the LIVE gauge-reg sandwich (LANDED, `L = 2`).** With `regStraighten.1 = deepestEFull`
(`hregval`): `conj-target =[regAbsorb_conj] gauge-reg+conjAbsorb =[Θ-peel @439] gauge-reg+bareAbsorb
=[regAbsorb_bare⁻¹] bare-target`. The two π̃ peels (`regAbsorbPeel_conj`/`_bare`) are LANDED via
`rlctAtOn_comp_localDiffeo` + the `DeepestL2ConjSmooth` `hTilde` lemmas. -/
theorem link2_at_zero_gaugeReg (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (hDA : ∀ s : Fin 2, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin 2, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0)
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hregval : ∀ q, (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q) :
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
  -- Rewrite `(regStraighten q).1` to `deepestEFull q` (hregval) under both `rlctAtOn` binders.
  simp only [hregval]
  -- conj-target = gauge-reg+conjAbsorb = gauge-reg+bareAbsorb = bare-target.
  rw [regAbsorb_conj H r B hB hr hL hDA hbdy J hJfront Pf Qf hPf hQf hQf0 hPfL hQf22 hPtri hQtri,
    ← rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb H r B hB hr hL hDA hbdy,
    ← regAbsorb_bare H r hr hL J Pf Qf hPf hQf hQf0 hPfL hQf22]

/-- **LINK-2 at flat `wstar`** — the `0`-form `link2_at_zero_gaugeReg` transported along the MP homeomorphism
`split` (`rlctAtOn_comp_homeomorph`, `split wstar = 0`). `rlctAtOn(R'∘split + coreF∘conjAbsorb∘split) wstar
= rlctAtOn(R'∘split + coreF∘bareAbsorb∘split) wstar`. -/
theorem link2_at_wstar_gaugeReg (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (hDA : ∀ s : Fin 2, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin 2, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0)
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hregval : ∀ q, (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q)
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
  -- Transport the `0`-form LINK2 to flat `wstar` via `rlctAtOn_comp_homeomorph split` (both sides).
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
  exact link2_at_zero_gaugeReg H r B hB hr hL hDA hbdy J hJfront Pf Qf hPf hQf hQf0 hPfL hQf22
    hPtri hQtri regStraighten hregval

/-- **The L=2 diffeo bridge, ASSEMBLED — the BARE canonical target, sorry-free.** `Φscore = R'∘split +
coreF∘BAREabsorb∘split` at `wstar`, the conclusion of `deepest_diffeo_bridge_L2` / the `hstep2` L=2 branch
consumes. Route: LINK1 (`deepest_diffeo_bridge_L2_conj_impl`, Φscore → conj target) ∘ the flat
`link2_at_wstar_gaugeReg` (conj → bare core). The TRUE conjugated hypotheses (`hsub3reg` conj via
`psiSplitRawL2CoreConj`, `hsub4core` conj) replace the bare `_impl`'s W-a-FALSE ones; `coreAbsorb` stays
BARE (route-b). The controller wires this into `deepest_gauge_construction`'s `hstep2`. -/
theorem deepest_diffeo_bridge_L2_assembled (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (hDA : ∀ s : Fin 2, IsUnit (deepBlkA H r B hB hr hL s))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin 2) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (hbdy : ∀ s : Fin 2, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit_mp : MeasurePreserving split volume volume)
    (hsub3reg : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
        nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      (∑ i, (deepestEFull H r hr hL J Pf Qf
          (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)) i) ^ 2)
        = ∑ i, (deepestEFull H r hr hL J Pf Qf (split x) i) ^ 2)
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (hregval : ∀ q, (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q)
    (Score : (Fin (flatDim H) → ℝ) → ℝ)
    (hsub4core : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
        nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
          (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x))).2.1 = Score x)
    (Φscore : (Fin (flatDim H) → ℝ) → ℝ)
    (hΦscore : Φscore = fun x => (∑ i, (regStraighten (split x)).1 i ^ 2) + Score x)
    (wstar : Fin (flatDim H) → ℝ)
    (hwstar : wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL)) :
    rlctAtOn Φscore wstar
      = rlctAtOn
          (fun x : Fin (flatDim H) → ℝ =>
            (∑ i, (regStraighten (split x)).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorb H r hr hL (split x)).2.1)
          wstar := by
  -- `split wstar = 0` (the basepoint, from `hsplit` + `hwstar`).
  have hsplit_wstar : split wstar = (0 : DeepestSplit H r (deepestNGauge H r)) := by
    rw [hsplit wstar]
    rw [show wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL) from hwstar]
    exact (deepestSplit_mp_basepoint H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))).2
  -- LINK1: `Φscore = conj target`.
  rw [deepest_diffeo_bridge_L2_conj_impl H r B hB hr hL rfl hDA hY hZ J Pf Qf split hsub3reg
      regStraighten hsplit hregval Score hsub4core Φscore hΦscore wstar hwstar]
  -- LINK2 (flat): conj target = bare target.
  exact link2_at_wstar_gaugeReg H r B hB hr hL hDA hbdy J hJfront Pf Qf hPf hQf hQf0 hPfL hQf22
    hPtri hQtri regStraighten hregval split hsplit_mp wstar hsplit_wstar

end DLNFibre.DLN.RLCT
