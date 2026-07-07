import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridge
import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeGenTheta

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeGenConj` — the general-`L` Step Ψ_conj reduction (#120 `hstep2`)

The general-`L` analog of the L=2 `deepest_diffeo_bridge_L2_conj_impl` / `deepest_diffeo_bridge_L2_assembled`
(`DeepestDiffeoBridgeL2Conj` / `DeepestL2ConjSub4`). This module supplies the **analytic reduction skeleton**
of the LINK-1 half of `hstep2 = Step Θ ∘ Step Ψ_conj`, and composes it with the LANDED general-`L`
Step Θ (`link2_at_wstar_gaugeReg_gen`, `DeepestDiffeoBridgeGenTheta`) to produce the `hstep2` conclusion.

## What is banked here (the plumbing, sorry-free)

* `deepest_diffeo_bridge_gen_conj_impl` — the general-`L` **conjugate** diffeo bridge, the LINK-1 half. It
  isolates the RLCT/diffeomorphism plumbing (`rlctAtOn_diffeo_bridge_of`) from the coupled geometric germs:
  given an abstract flat local diffeo `psi` at `wstar` (ContDiff `⊤`, strict derivative the identity, fixing
  `wstar`), its split-side action `psiSplitRaw` (the germ `split ∘ psi =ᶠ psiSplitRaw ∘ split`), and the two
  coupled germs — reg-preservation `hsub3reg` and core-to-`Score` `hsub4core` — it reduces
  `rlctAtOn Φscore wstar` to the **conjugate** absorbed-core target
  `rlctAtOn (∑ (regStraighten (split x))² + coreF(deepestCoreAbsorbConj (split x))) wstar`.
  Mirrors `deepest_diffeo_bridge_L2_conj_impl` abstracting over the concrete `psiL2Conj`/`psiSplitRawL2CoreConj`.

* `deepest_diffeo_bridge_gen_assembled` — composes the LINK-1 reduction with the LANDED general Step Θ
  (`link2_at_wstar_gaugeReg_gen`): the conjugate target `= ` the **bare** absorbed-core target
  `rlctAtOn (∑ (regStraighten (split x))² + coreF(deepestCoreAbsorb (split x))) wstar` — exactly the RHS the
  `hstep2` sorry (`DeepestL2Wiring:1060`, L ≥ 3 arm) consumes. Mirrors `deepest_diffeo_bridge_L2_assembled`.

## What remains (the coupled bulk — a separate tide, `HONEST-PARTIAL`)

The two germs `hsub3reg`/`hsub4core` and the concrete general `psi`/`psiSplitRaw` (the general Ψ_conj) are
NOT discharged here — they are the **coupled geometric bulk**, comparable in size to the entire L=2 conj
machinery (`DeepestDiffeoBridgeL2Conj.lean`, ~2700 lines) plus the honest chain identity
`blockSchur(partProd Ĉ L) = ScoreSchur` (numerically certified, not yet in Lean). The general `psiSplitRaw`
is NOT a pure core-shear conjugation (`deepestCoreAbsorbConj⁻¹ ∘ Ψ ∘ deepestCoreAbsorbConj`): a pure core
shear changes `deepestEFull` (which reads the core slot via `framedParamsPivot`), breaking `hsub3reg`. It
must be the L=2 **joint move** — a core shear plus a canonical reg/gauge fibre correction that keeps
`deepestEFull` exactly invariant while the core-edit realises the Schur untwisting to `Score`. This
reduction states `psi`, `psiSplitRaw`, the diffeo triple, the split-compatibility germ, and the two germs
as explicit hypotheses (Codex-vetted as a faithful reduction, not laundering: it does not pretend the hard
construction is done). The `hstep2` sorry is therefore LEFT UNTOUCHED pending the coupled bulk.
-/

open MeasureTheory Topology Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The general-`L` conjugate diffeo bridge (LINK-1, the analytic reduction).** Given an abstract flat
local diffeo `psi` at `wstar` (`hcontdiff`/`hderiv`/`hfix`) whose split-side action is `psiSplitRaw`
(`hsplitPsi : split ∘ psi =ᶠ[𝓝 wstar] psiSplitRaw ∘ split`), and the two coupled germs
* **`hsub3reg`** — reg preservation: `∑ (regStraighten (psiSplitRaw (split x)))².1 = ∑ (regStraighten (split x)))².1`;
* **`hsub4core`** — core untwisting: `coreF(deepestCoreAbsorbConj (psiSplitRaw (split x))).2.1 = Score x`,

the two RLCTs agree: `rlctAtOn Φscore wstar = rlctAtOn Φcore_conj wstar`, where `Φcore_conj` is the
**conjugate** absorbed-core energy `∑ (regStraighten (split x))².1 + coreF(deepestCoreAbsorbConj (split x))`.
Proof: the three germs give `Φcore_conj ∘ psi =ᶠ[𝓝 wstar] Φscore`, and `rlctAtOn_diffeo_bridge_of` strips
the diffeo. Mirrors `deepest_diffeo_bridge_L2_conj_impl`, abstracting over the concrete `psiL2Conj` /
`psiSplitRawL2CoreConj`; the conjugate target is the LHS of Step Θ (`link2_at_wstar_gaugeReg_gen`). -/
theorem deepest_diffeo_bridge_gen_conj_impl (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (psi : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ))
    (psiSplitRaw : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (wstar : Fin (flatDim H) → ℝ)
    (hcontdiff : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hderiv : HasStrictFDerivAt psi
      (ContinuousLinearMap.id ℝ (Fin (flatDim H) → ℝ)) wstar)
    (hfix : psi wstar = wstar)
    (hsplitPsi : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds wstar,
      split (psi x) = psiSplitRaw (split x))
    (hsub3reg : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds wstar,
      (∑ i, (regStraighten (psiSplitRaw (split x))).1 i ^ 2)
        = ∑ i, (regStraighten (split x)).1 i ^ 2)
    (Score : (Fin (flatDim H) → ℝ) → ℝ)
    (hsub4core : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds wstar,
      deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
        (psiSplitRaw (split x))).2.1 = Score x)
    (Φscore : (Fin (flatDim H) → ℝ) → ℝ)
    (hΦscore : Φscore = fun x => (∑ i, (regStraighten (split x)).1 i ^ 2) + Score x) :
    rlctAtOn Φscore wstar
      = rlctAtOn
          (fun x : Fin (flatDim H) → ℝ =>
            (∑ i, (regStraighten (split x)).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA (split x)).2.1)
          wstar := by
  set Φcore : (Fin (flatDim H) → ℝ) → ℝ :=
    fun x => (∑ i, (regStraighten (split x)).1 i ^ 2)
      + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA (split x)).2.1 with hΦcore
  have hcomp : (fun x => Φcore (psi x)) =ᶠ[nhds wstar] Φscore := by
    filter_upwards [hsplitPsi, hsub3reg, hsub4core] with x hsp hs3 hs4
    change (∑ i, (regStraighten (split (psi x))).1 i ^ 2)
        + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA (split (psi x))).2.1
      = Φscore x
    rw [hsp, hΦscore, hs3, hs4]
  exact rlctAtOn_diffeo_bridge_of Φscore Φcore wstar psi
    (ContinuousLinearEquiv.refl ℝ (Fin (flatDim H) → ℝ)) hcontdiff hderiv hfix hcomp

/-- **The general-`L` diffeo bridge, ASSEMBLED — the BARE canonical target.** Composes the LINK-1
reduction (`deepest_diffeo_bridge_gen_conj_impl`, Φscore → conjugate target) with the LANDED general
Step Θ (`link2_at_wstar_gaugeReg_gen`, conjugate → bare) to produce `rlctAtOn Φscore wstar =
rlctAtOn (∑ (regStraighten (split x))² + coreF(deepestCoreAbsorb (split x))) wstar`,
the RHS the `hstep2` sorry (`DeepestL2Wiring:1060`, L ≥ 3 arm) consumes. Mirrors
`deepest_diffeo_bridge_L2_assembled`. The germs / concrete diffeo (the coupled bulk) enter as
hypotheses; this is the faithful reduction that isolates the plumbing from that bulk. -/
theorem deepest_diffeo_bridge_gen_assembled (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit_mp : MeasurePreserving split volume volume)
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hregval : ∀ q, (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q)
    (psi : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ))
    (psiSplitRaw : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (wstar : Fin (flatDim H) → ℝ)
    (hsplit_wstar : split wstar = (0 : DeepestSplit H r (deepestNGauge H r)))
    (hcontdiff : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hderiv : HasStrictFDerivAt psi
      (ContinuousLinearMap.id ℝ (Fin (flatDim H) → ℝ)) wstar)
    (hfix : psi wstar = wstar)
    (hsplitPsi : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds wstar,
      split (psi x) = psiSplitRaw (split x))
    (hsub3reg : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds wstar,
      (∑ i, (regStraighten (psiSplitRaw (split x))).1 i ^ 2)
        = ∑ i, (regStraighten (split x)).1 i ^ 2)
    (Score : (Fin (flatDim H) → ℝ) → ℝ)
    (hsub4core : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds wstar,
      deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
        (psiSplitRaw (split x))).2.1 = Score x)
    (Φscore : (Fin (flatDim H) → ℝ) → ℝ)
    (hΦscore : Φscore = fun x => (∑ i, (regStraighten (split x)).1 i ^ 2) + Score x) :
    rlctAtOn Φscore wstar
      = rlctAtOn
          (fun x : Fin (flatDim H) → ℝ =>
            (∑ i, (regStraighten (split x)).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorb H r hr hL (split x)).2.1)
          wstar := by
  -- LINK-1: `Φscore → conjugate target`.
  rw [deepest_diffeo_bridge_gen_conj_impl H r B hB hr hL hDA split regStraighten psi psiSplitRaw
      wstar hcontdiff hderiv hfix hsplitPsi hsub3reg Score hsub4core Φscore hΦscore]
  -- LINK-2 (Step Θ, flat): conjugate target → bare target.
  exact link2_at_wstar_gaugeReg_gen H r B hB hr hL hL2 hDA hbdy J hJfront Pf Qf hPf hQf hQf0 hPfL
    hQf22 hPtri hQtri regStraighten hregval split hsplit_mp wstar hsplit_wstar

end DLNFibre.DLN.RLCT
