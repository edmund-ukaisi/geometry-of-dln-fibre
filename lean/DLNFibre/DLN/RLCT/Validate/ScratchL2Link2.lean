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

**The single remaining residual — closes by COMPARABILITY, not a diffeo (decided 2026-06-29,
decorrelated cert origin/genm-l2wire2 @f934c748).** The Θ-peeled LHS has reg argument `Θ q` (not `q`).
Matching it to the conj LINK2 side is
`rlctAtOn (∑(regStraighten (Θ q)).1² + C q) 0 = rlctAtOn (∑(regStraighten q).1² + C q) 0`, `C = coreF∘conjAbsorb`.
A reg-side diffeo does NOT exist (none fixes `C`; the leak is bilinear core↔reg). It closes by **Watanabe
two-sided comparability** `rlctAtOn_squeeze` (`S1NonMPTransport:119`): `F, Φ ≥ 0`, measurable, and
`c₁·Φ ≤ F ≤ c₂·Φ` on a nbhd of `0` ⟹ equal `rlctAtOn`. Here `Φ = ∑R'(q)² + C`, `F = ∑R'(Θq)² + C`; `C`
CANCELS in `F − Φ = ∑(2R'(q)·ΔR + ΔR²)` (`ΔR = R'(Θq)−R'(q)`), and the ε-bound `|F − Φ| ≤ ε·∑R'² ≤ ε·Φ`
comes from the load-bearing triple: (i) the atom `deepestEFull_coreConstant` (`R'(0,c,0)=R'(0,0,0)`) ⟹ `ΔR`
carries a reg factor (vanishes at reg=0); (ii) `Θ0=0` ⟹ the core shift `delta` →0; (iii) PIN-1 `dE(0)`
invertible ⟹ `∑R'² ≳ ‖reg‖²` dominates. `C`'s DLN core-degeneracy NEVER enters the denominator (only
`F ≥ ∑R'² ≥ 0` is used). `link2_rho_residual` (HELD — the ε-bound, the genuine analytic residual).

**`link2_at_zero`** chains: `link2_rho_residual` ▸ `link2_thetaPeel_half`. -/

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

/-- **The ε-bound for the comparability close (HELD — the genuine analytic residual).** On a nbhd of `0`,
the two integrands `Φ = ∑R'(q)² + C` and `F = ∑R'(Θq)² + C` (`C = coreF∘conjAbsorb`, `R' = regStraighten·`)
satisfy the Watanabe two-sided bound with `c₁ = 1/2`, `c₂ = 3/2`. The load-bearing triple: the atom
`deepestEFull_coreConstant` (`ΔR = R'(Θq)−R'(q)` carries a reg factor), `Θ0=0` (the core shift →0), and
PIN-1 `dE(0)` invertible (`∑R'² ≳ ‖reg‖²` dominates) ⟹ `|F − Φ| ≤ (1/2)·∑R'² ≤ (1/2)·Φ`. The `regStraighten`
is the wire's `regStraightenOf2 (deepestEFull ∘ coreAbsorb.symm)`; `hregcont` carries its continuity (for
measurability). Held: the ε-estimate over the actual objects (a bounded analytic tide-leg). -/
theorem rho_residual_epsBound (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r)) :
    ∃ U ∈ nhds (0 : DeepestSplit H r (deepestNGauge H r)),
      ∀ q ∈ U,
        0 ≤ (∑ i, (regStraighten q).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1
        ∧ (1/2 : ℝ) * ((∑ i, (regStraighten q).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
            ≤ (∑ i, (regStraighten (thetaConj H r B hB hr hL hDA q)).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1
        ∧ (∑ i, (regStraighten (thetaConj H r B hB hr hL hDA q)).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1
            ≤ (3/2 : ℝ) * ((∑ i, (regStraighten q).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1) := by
  sorry

/-- **The single residual — the reg-argument swap `Θ q ↦ q` under `rlctAtOn`, core `C` fixed both sides.**
Closes by Watanabe two-sided comparability (`rlctAtOn_squeeze`) — NOT a diffeo. `F, Φ ≥ 0` + measurable
(`regStraighten`/`Θ`/`deepestCoreF`/`conjAbsorb` continuous) + the ε-bound `rho_residual_epsBound`. -/
theorem link2_rho_residual (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hregcont : Continuous regStraighten) :
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
  -- Measurability of both integrands (reg sum-of-squares + the continuous conj core energy).
  -- `deepestCoreF y = dlnLoss (deepestM) 0 (decode y)`, continuous in `y`; precomposed with the
  -- continuous `conjAbsorb` and the `.2.1` projection.
  have hCcont : Continuous (fun q : DeepestSplit H r (deepestNGauge H r) =>
      deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1) :=
    ((continuous_dlnLoss (deepestM H r)
        (0 : Matrix (Fin (deepestM H r 0)) (Fin (deepestM H r (Fin.last L))) ℝ)).comp
      (continuous_paramsEquivFlat_symm (deepestM H r))).comp
      ((continuous_fst.comp continuous_snd).comp
        (deepestCoreAbsorbConj H r B hB hr hL hDA).continuous)
  have hΘcont : Continuous (thetaConj H r B hB hr hL hDA) :=
    (thetaConj H r B hB hr hL hDA).continuous
  have hΦmeas : Measurable (fun q : DeepestSplit H r (deepestNGauge H r) =>
      (∑ i, (regStraighten q).1 i ^ 2)
        + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1) :=
    ((Finset.measurable_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp (continuous_fst.comp hregcont).measurable).pow_const _))).add
      hCcont.measurable
  have hFmeas : Measurable (fun q : DeepestSplit H r (deepestNGauge H r) =>
      (∑ i, (regStraighten (thetaConj H r B hB hr hL hDA q)).1 i ^ 2)
        + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1) :=
    ((Finset.measurable_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp
        (continuous_fst.comp (hregcont.comp hΘcont)).measurable).pow_const _))).add
      hCcont.measurable
  -- The squeeze: with `F = moved` (∑R'(Θq)²+C), `Φ = unmoved` (∑R'(q)²+C), the ε-bound is `c₁·Φ ≤ F ≤ c₂·Φ`.
  -- `rlctAtOn_squeeze` gives `rlctAtOn F = rlctAtOn Φ`; the goal is `rlctAtOn Φ = rlctAtOn F`, so `.symm`.
  exact (rlctAtOn_squeeze
    (fun q : DeepestSplit H r (deepestNGauge H r) =>
      (∑ i, (regStraighten (thetaConj H r B hB hr hL hDA q)).1 i ^ 2)
        + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
    (fun q : DeepestSplit H r (deepestNGauge H r) =>
      (∑ i, (regStraighten q).1 i ^ 2)
        + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
    (0 : DeepestSplit H r (deepestNGauge H r)) hFmeas hΦmeas
    (1/2) (3/2) (by norm_num) (by norm_num)
    (rho_residual_epsBound H r B hB hr hL hDA regStraighten)).symm

/-- **LINK-2 at `0 : DeepestSplit`** (the bare↔conjugated absorbed-core RLCT bridge, `regStraighten` reg
term). `link2_rho_residual` (HELD, the ρ-cert) ▸ `link2_thetaPeel_half` (BANKED). The flat-`wstar` form the
wire consumes follows by the `split` reparametrization (`rlctAtOn_comp_homeomorph split`, separate wire). -/
theorem link2_at_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hregcont : Continuous regStraighten) :
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
  (link2_rho_residual H r B hB hr hL hDA regStraighten hregcont).trans
    (link2_thetaPeel_half H r B hB hr hL hDA hbdy regStraighten)

end DLNFibre.DLN.RLCT
