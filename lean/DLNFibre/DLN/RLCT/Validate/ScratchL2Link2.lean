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

/-- **DEAD — do NOT build (comparability REFUTED, 2026-06-29).** The two-sided bound `c₁·Φ ≤ F ≤ c₂·Φ`
this lemma asserts is FALSE: `F = ∑R'(Θq)²+C` and `Φ = ∑R'(q)²+C` have DIFFERENT zero sets (exact-rational
witnesses, a44dd7e4 + here-verified, `docs/decorrelated-records/link2-fork/codex_fix_witnesses.py`: W1 `F=0,
Φ>0`; W2 `Φ=0, F>0`; W3 `F/Φ→∞`). So `rho_residual_epsBound` is UNBUILDABLE and the comparability route to
`link2_rho_residual` is dead. All three candidate fixes (atom+, δ-reg-factor, spec-PIN) fail by exact algebra.

**The LIVE replacement route** (does NOT use this lemma): drop the reg level from `deepestEFull` (where `Θ`
DRAGS) to the GAUGE reg `∑q.1²` (where `Θ` FIXES `q.1`), apply the BANKED Θ-peel
`rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb` (DeepestSchurShiftConj:439, sorry-free, gauge-reg level, NO drag),
then lift back — via the `rlctAtOn_regAbsorb_reduce2` (π̃ option-D) LOCAL-DIFFEO reg-absorb for both bare and
conj `coreAbsorb`. Local diffeos preserve zero sets, so the comparability obstruction does not re-appear.
Cost: the wire's `hTilde` reg-absorb strict-deriv (bare, in-flight) + a conj twin. This `sorry` is a DEAD
MARKER, retained only so `link2_rho_residual`/`link2_at_zero` below still typecheck as the OLD (dead) shape;
they are superseded by the gauge-reg sandwich and must NOT be wired to canonical. -/
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

/-- **DEAD (depends on the refuted `rho_residual_epsBound`) — superseded by the gauge-reg Θ-peel sandwich.**
The reg-argument swap `Θ q ↦ q` (core `C` fixed) does NOT hold by comparability — `F`,`Φ` have different
zero sets (see `rho_residual_epsBound`). Retained only so the (dead) `link2_at_zero` shape typechecks; the
live close-path uses `rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb` at the GAUGE-reg level + `rlctAtOn_regAbsorb_reduce2`,
NOT this. Do NOT wire to canonical. -/
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

/-! ### The LIVE route — the gauge-reg Θ-peel sandwich (SPECIFY skeleton).

Replaces the dead `link2_rho_residual`/`link2_at_zero`. LINK2 (conj→bare core, at `0 : DeepestSplit`,
`regStraighten` reg term) closes by dropping to the GAUGE reg `∑q.1²` — where the BANKED Θ-peel
`rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb` (@439) converts bare↔conj with NO drag (`Θ` fixes `q.1`) — and
lifting back via the `rlctAtOn_regAbsorb_reduce2` (π̃ option-D) LOCAL-DIFFEO reg-absorb (which preserves zero
sets, so the dead comparability does not recur). Two `hpeel` residuals (HELD pending a44dd7e4's π̃-invertibility
cert): the conj reg-absorb and the bare reg-absorb (= the wire's `hTilde` strict-deriv). -/

/-- **π̃ reg-absorb peel, CONJ side (HELD — π̃-conj invertibility, a44dd7e4 cert pending).** The `hpeel` input
`rlctAtOn_regAbsorb_reduce2` needs for `coreAbsorb := conjAbsorb`, `E := deepestEFull`: the conjugated π̃
`q ↦ (deepestEFull (conjAbsorb.symm q), q.2)` is a local diffeo at `0` (`HasStrictFDerivAt` an `≃L` =
the core-shear ∘ the `regStraightenTotalCLM2 (dE)` shear, both invertible under `hDA`), so
`rlctAtOn_comp_localDiffeo` peels it: `rlctAtOn(∑(deepestEFull (conjAbsorb.symm q))² + ∑q.2.1²-core) 0
= rlctAtOn(∑q.1² + …) 0`. The conj analogue of the wire's bare `hTilde`. -/
theorem regAbsorbPeel_conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
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
  sorry

/-- **π̃ reg-absorb peel, BARE side (HELD — = the wire's `hTilde` strict-deriv, in-flight).** The bare
analogue of `regAbsorbPeel_conj` (`coreAbsorb := deepestCoreAbsorb`): the bare π̃
`q ↦ (deepestEFull (deepestCoreAbsorb.symm q), q.2)` is a local diffeo at `0` (the degree-2 core-block
vanishing `∂deepestEFull/∂core(0)=0` keeps π̃'s reg-reg block PIN1's invertible `F` despite the
`coreAbsorb.symm` reg→core shear). IS the wire's `hTilde` (DeepestL2Wiring:238). -/
theorem regAbsorbPeel_bare (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
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
  sorry

/-- **The gauge-reg reg-absorb (CONJ), via `rlctAtOn_regAbsorb_reduce2` + `regAbsorbPeel_conj`.** Straightens
the `deepestEFull` reg output down to the gauge reg `∑q.1²`, holding the CONJ core absorb fixed. -/
theorem regAbsorb_conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
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
    (regAbsorbPeel_conj H r B hB hr hL hDA J Pf Qf)

/-- **The gauge-reg reg-absorb (BARE), via `rlctAtOn_regAbsorb_reduce2` + `regAbsorbPeel_bare`.** -/
theorem regAbsorb_bare (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
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
    (regAbsorbPeel_bare H r B hB hr hL J Pf Qf)

/-- **LINK-2 at `0` — the LIVE gauge-reg sandwich.** With `regStraighten.1 = deepestEFull` (`hregval`):
`conj-target =[regAbsorb_conj] gauge-reg+conjAbsorb =[Θ-peel @439] gauge-reg+bareAbsorb =[regAbsorb_bare⁻¹]
bare-target`. Modulo the two π̃ peels (`regAbsorbPeel_conj`/`_bare`, HELD). -/
theorem link2_at_zero_gaugeReg (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
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
  rw [regAbsorb_conj H r B hB hr hL hDA hbdy J Pf Qf,
    ← rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb H r B hB hr hL hDA hbdy,
    ← regAbsorb_bare H r B hB hr hL J Pf Qf]

end DLNFibre.DLN.RLCT
