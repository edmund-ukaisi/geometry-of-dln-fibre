import DLNFibre.DLN.RLCT.Validate.DeepestL2Wiring
import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2Conj
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShiftConj

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

**The single remaining ρ-residual.** The Θ-peeled LHS has reg argument `Θ q` (not `q`). Matching it to the
conj LINK2 side needs ONE reg-side diffeo `ρ` (core+spec-fixing) closing
`rlctAtOn (∑(regStraighten (Θ q)).1² + C q) 0 = rlctAtOn (∑(regStraighten q).1² + C q) 0`, `C = coreF∘conjAbsorb`.
This is NOT a pointwise equality (`deepestEFull(Θ q) ≠ deepestEFull(q)`: `deepestEFull` reads the core,
`deepestEFull_coreZero` drops it only at core 0; `Θ` shifts the core) — it needs the genm-l2regadj ρ-cert
(the reg-block-only core-fix diffeo, 3 inputs: ContDiff via the reg block [NO conj-`d`], strict-deriv det=1
≃L at 0, fixpoint). HELD pending the ρ-cert; stated as `link2_rho_residual` (correct statement, route-b).

**`link2_via_nf`** then chains: `link2_rho_residual` ▸ `link2_thetaPeel_half`. (The "NF" framing collapses to
ONE ρ since the Θ-peel discharges the bare side — half the original two-sided NF.) -/

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

/-- **The single ρ-residual (HELD — the genm-l2regadj ρ-cert).** The reg-argument swap `Θ q ↦ q` under
`rlctAtOn`, with the SAME conjugated core both sides. Closed by ONE reg-side core+spec-fixing diffeo `ρ`
(`rlctAtOn_comp_localDiffeo`/`rlctAtOn_diffeo_bridge_of`). Stated at `0 : DeepestSplit`, route-b. -/
theorem link2_rho_residual (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r)) :
    rlctAtOn
        (fun q : DeepestSplit H r (deepestNGauge H r) =>
          (∑ i, (regStraighten q).1 i ^ 2)
            + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
        (0 : DeepestSplit H r (deepestNGauge H r))
      = rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, (regStraighten (thetaConj H r B hB hr hL hDA q)).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r)) := by
  sorry

/-- **LINK-2 at `0 : DeepestSplit`** (the bare↔conjugated absorbed-core RLCT bridge, `regStraighten` reg
term). `link2_rho_residual` (HELD, the ρ-cert) ▸ `link2_thetaPeel_half` (BANKED). The flat-`wstar` form the
wire consumes follows by the `split` reparametrization (`rlctAtOn_comp_homeomorph split`, separate wire). -/
theorem link2_at_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r)) :
    rlctAtOn
        (fun q : DeepestSplit H r (deepestNGauge H r) =>
          (∑ i, (regStraighten q).1 i ^ 2)
            + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
        (0 : DeepestSplit H r (deepestNGauge H r))
      = rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, (regStraighten q).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r)) :=
  (link2_rho_residual H r B hB hr hL hDA regStraighten).trans
    (link2_thetaPeel_half H r B hB hr hL hDA hbdy regStraighten)

end DLNFibre.DLN.RLCT
