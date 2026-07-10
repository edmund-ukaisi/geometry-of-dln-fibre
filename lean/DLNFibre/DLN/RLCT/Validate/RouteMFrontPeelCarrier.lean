import DLNFibre.DLN.RLCT.Validate.RouteMSJJointReduce
import DLNFibre.DLN.RLCT.Validate.RouteMFrontPeelCharge
import DLNFibre.DLN.RLCT.Validate.RouteMFrontBottleneck
import DLNFibre.DLN.RLCT.Validate.RadialResidualPower
import DLNFibre.DLN.RLCT.Validate.RouteMSJThreadedShear
import DLNFibre.DLN.RLCT.Validate.DeepestCoreNonvanishing

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMFrontPeelCarrier` — the FRONT-PEEL carrier (wiring W1)

**Thread `genm-fpcarrier`, Stage 2.** The single-writer carrier that discharges
`(□) = RouteMBoxThresholdFinite M` (∀ nondegenerate `M`) via the FRONT-PEEL primitive
`A₀ ↦ A₀·U` (r1substratum §C), then closes the canonical open leaf `sjJointResolution` as a
corollary (wiring W1).

## The route (why front-peel, and why it terminates)

The recursion peels the LEADING layer `A₀` against the tail product `P = prod (tailChain M) A'`,
stratified by `rank P = q`. On the stratum `{rank P = q}` the map `A₀ ↦ A₀·U` (with `U` a
full-column-rank basis of `im P`) is a linear surjection onto `M₀ × q` with kernel dimension
`M₀·(M₁−q)`: an isotropic `M₀·q` Morse block plus a bounded kernel box, giving the exponent shift
`M₀·q/2`. The deeper factor is the tail-rank locus `{rank P ≤ q}`, whose singularity type equals
(normal-slice isomorphism, paper Thm `addlongest`) that of `Σ⁰` of the SHIFTED chain
`(M₁−q, …, M_L−q) = fun i => M i.succ - q`, a chain of arity strictly one lower. That shifted chain
is exactly the argument of the strong induction hypothesis in `SJStepHyp`, so the front-peel step
is a `SJStepHyp` and the banked arity strong-induction wrapper `routeMBoxThresholdFinite_of_step`
supplies termination (arity strictly drops).

The ℕ accounting closes: `frontCharge_ge_minAdm` gives `minAdm M ≤ M₀·q + minAdm (shifted)`, so the
shifted exponent `c' − M₀·q/2` stays below `½·minAdm (shifted)` (`shiftedThreshold`), exactly the
IH's threshold. Case-2 (Aoyagi's residual-block divisor) never binds `(□)`
(`minAdm M ≤ M(S)·M^(S+1)`) and is subsumed by this `minAdm` accounting — no separate branch.

## What is stated here

* `frontStratumIntegral M q c'` — the per-tail-rank-`q` contribution to the front-split box integral
  (the front-split integrand, outer domain restricted to `{rank P = q}`).
* `shiftedThreshold` — PROVED. The charge accounting: `q ≤ tailMin M`, `c' < ½·minAdm M` ⟹
  `c' − M₀·q/2 < ½·minAdm (fun i => M i.succ − q)`. Pure arithmetic from `frontCharge_ge_minAdm`.
* `outerRankCover` — PROVED. The front-split box integral is bounded by the finite sum over
  `q = 0..tailMin M` of the stratum contributions.
* `morse_reduced_box_lt_top` — PROVED (regime dispatch; borderline `c'=d/2` a named sorry). The
  reduced-chain box with a `d`-dim isotropic Morse block is finite below `½·(d+minAdm R)`: `d=0` by
  `hIH`, regime B by `radial_morse_dominates_absZ_lt_top`, regime A by `morseCore_residual_lt_top`.
* `reducedMorseFront` / `reducedMorseFront_lt_top` — PROVED (radius 1). The per-chart CoV-image
  endpoint (`d = M₀q`, `R = redTail M q`), finite below `½·minAdm M` via `morse_reduced_box_lt_top` +
  `frontCharge_ge_minAdm`.
* `NormalSliceChartData` / `normalSlice_transfer_of_data` — the interface (route A) + assembly
  (route B, PROVED): the stratum contribution reduces to a finite chart family, each finite (the
  above endpoint); a finite sum of finite terms is finite.
* `normalSlice_transfer` — PROVED via the datum. On the `{rank P = q}` stratum the contribution is
  finite given `hIH`. The residue is the datum constructor `normalSliceChartData` (NAMED SORRY, the
  threaded-shear CoV at opaque widths, vslice `normalslice-cert.md` §2–4).
* `frontPeelStep_proof : SJStepHyp` — PROVED (modulo the sorries), composing `outerRankCover` +
  `normalSlice_transfer`. The front-peel inductive step.
* `routeMBoxThresholdFinite_frontPeel` — PROVED (modulo the sorries): `RouteMBoxThresholdFinite M`
  ∀M, via `routeMBoxThresholdFinite_of_step frontPeelStep_proof sjBase1_freeMatrix`.
* `sjJointResolution_frontPeel` — PROVED (modulo the sorries): the canonical `sjJointResolution`
  statement, re-proved via `sjJointResolution_of_boxThresholdFinite` applied to the INDEPENDENT
  front-peel box-finiteness (NOT through the spine — circular, per `RouteMSJJointReduce`'s header).
  The drop-in the controller wires to discharge the canonical `RouteMSJResolution.lean:803` sorry.

**Branch discipline.** All gaps live on branch `genm-threadedshear`; canonical stays 0-sorry/0-axiom.
The three remaining `sorry`s are all TRUE statements: `normalSliceChartData` (the datum exists — the
opaque-width threaded shear + loss split + finite pivot cover), `morse_reduced_box_lt_top`'s borderline
`c' = d/2` (the log endpoint), and `reduced_frobSq_ae_pos` (the regime-A reduced-chain nondegeneracy).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## The per-tail-rank stratum contribution -/

/-- **The tail-rank-`q` stratum contribution to the front-split box integral.** The front-split
integrand `frobSq(A₀ · prod(tailChain M) A')^{−c'}`, integrated over the leading-layer box (inner,
`A₀`) and the tail box restricted to the exact-rank stratum
`{A' | rank(prod (tailChain M) A') = q}` (outer, `A'`). The `q`-th term of the front-peel cover of
`routeMLayerBoxIntegral M c' 1`. -/
noncomputable def frontStratumIntegral (M : Fin (L + 1 + 1 + 1) → ℕ) (q : ℕ) (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ A' in paramsBoxM (tailChain M) 1 ∩
      {A' : Params (tailChain M) | (prod (tailChain M) A').rank = q},
    ∫⁻ A0 in matBox (M 0) (M 1) 1,
      ENNReal.ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c'))

/-! ## The charge accounting (PROVED) -/

/-- **The shifted-exponent stays below the shifted-chain threshold (PROVED).** For an admissible
tail-rank `q ≤ tailMin M` and `c' < ½·minAdm M`, the front-peel-shifted exponent `c' − M₀·q/2` is
below `½·minAdm` of the shifted chain `(fun i => M i.succ − q)`. This is the threshold the strong
induction hypothesis `RouteMBoxThresholdFinite (fun i => M i.succ − q)` requires at the shifted
exponent. Immediate from the front-peel inequality `frontCharge_ge_minAdm`
(`minAdm M ≤ M₀·q + minAdm (fun i => M i.succ − q)`), cast to `ℝ`. -/
theorem shiftedThreshold (M : Fin (L + 1 + 1 + 1) → ℕ) (q : ℕ) (hq : q ≤ tailMin M)
    (c' : ℝ) (hc' : c' < (minAdm M : ℝ) / 2) :
    c' - (M 0 * q : ℝ) / 2 < (minAdm (fun i : Fin (L + 1 + 1) => M i.succ - q) : ℝ) / 2 := by
  have h := frontCharge_ge_minAdm M q hq
  unfold frontCharge at h
  have hc : (minAdm M : ℝ)
      ≤ (M 0 * q : ℝ) + (minAdm (fun i : Fin (L + 1 + 1) => M i.succ - q) : ℝ) := by
    exact_mod_cast h
  linarith

/-! ## The front-peel cover (PROVED — routine measure theory) -/

/-- **The tail product has rank `≤ tailMin M`.** Each tail width `M j.succ = tailChain M j` bounds
the product's rank: `prodAux_split_exists` factors `prod (tailChain M) A'` through position `j`
(`prod = prodAux j * Y`), so `rank ≤ rank(prodAux j) ≤` the column count `tailChain M j`
(`rank_le_width`). Taking the inf over `j` gives `tailMin M`. -/
theorem prod_tailChain_rank_le_tailMin (M : Fin (L + 1 + 1 + 1) → ℕ) (A' : Params (tailChain M)) :
    (prod (tailChain M) A').rank ≤ tailMin M := by
  rw [tailMin, Finset.le_inf'_iff]
  intro j _
  obtain ⟨Y, hY⟩ := prodAux_split_exists (tailChain M) A' (j : ℕ) j.isLt (L + 1)
    (Nat.lt_succ_iff.mp j.isLt) (Nat.lt_succ_self (L + 1))
  calc (prod (tailChain M) A').rank
      = (prodAux (tailChain M) A' (L + 1) (Nat.lt_succ_self (L + 1))).rank := rfl
    _ = (prodAux (tailChain M) A' (j : ℕ) j.isLt * Y).rank := by rw [hY]
    _ ≤ (prodAux (tailChain M) A' (j : ℕ) j.isLt).rank := Matrix.rank_mul_le_left _ _
    _ ≤ M j.succ := Matrix.rank_le_width _

/-- **The front-split box integral is covered by the finite tail-rank stratification (PROVED).** For
every `c'`, `routeMLayerBoxIntegral M c' 1 ≤ ∑_{q=0}^{tailMin M} frontStratumIntegral M q c'`. The
banked front-split `routeMLayerBoxIntegral_front_split` rewrites to the tail-outer front-factor
integral; the outer tail box partitions as `⋃_{q ≤ tailMin M} {rank(prod (tailChain M) A') = q}`
(rank `≤ tailMin M` everywhere, `prod_tailChain_rank_le_tailMin`); `lintegral_iUnion_le` +
`tsum_fintype` collapse the finite union to the `Finset.range (tailMin M + 1)` sum. -/
theorem outerRankCover (M : Fin (L + 1 + 1 + 1) → ℕ) (c' : ℝ) :
    routeMLayerBoxIntegral M c' 1
      ≤ ∑ q ∈ Finset.range (tailMin M + 1), frontStratumIntegral M q c' := by
  have hcov : paramsBoxM (tailChain M) 1
      = ⋃ i : Fin (tailMin M + 1),
          (paramsBoxM (tailChain M) 1 ∩
            {A' : Params (tailChain M) | (prod (tailChain M) A').rank = (i : ℕ)}) := by
    apply Set.ext
    intro A'
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hA'
      exact ⟨⟨(prod (tailChain M) A').rank,
          Nat.lt_succ_of_le (prod_tailChain_rank_le_tailMin M A')⟩, hA', rfl⟩
    · rintro ⟨_, hA', _⟩; exact hA'
  rw [routeMLayerBoxIntegral_front_split M c', hcov]
  calc ∫⁻ A' in (⋃ i : Fin (tailMin M + 1),
            (paramsBoxM (tailChain M) 1 ∩
              {A' : Params (tailChain M) | (prod (tailChain M) A').rank = (i : ℕ)})),
          ∫⁻ A0 in matBox (M 0) (M 1) 1,
            ENNReal.ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c'))
      ≤ ∑' i : Fin (tailMin M + 1),
          ∫⁻ A' in (paramsBoxM (tailChain M) 1 ∩
              {A' : Params (tailChain M) | (prod (tailChain M) A').rank = (i : ℕ)}),
            ∫⁻ A0 in matBox (M 0) (M 1) 1,
              ENNReal.ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c')) :=
        lintegral_iUnion_le _ _
    _ = ∑ i : Fin (tailMin M + 1),
          ∫⁻ A' in (paramsBoxM (tailChain M) 1 ∩
              {A' : Params (tailChain M) | (prod (tailChain M) A').rank = (i : ℕ)}),
            ∫⁻ A0 in matBox (M 0) (M 1) 1,
              ENNReal.ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c')) :=
        tsum_fintype _
    _ = ∑ q ∈ Finset.range (tailMin M + 1), frontStratumIntegral M q c' :=
        Fin.sum_univ_eq_sum_range (fun q => frontStratumIntegral M q c') (tailMin M + 1)

/-! ## The additive endpoint (PROVED — regime A exponent shift + IH) -/

/-- **The additive Morse-block + core endpoint, regime A (PROVED).** A `(m+1)`-dim Morse block `P`
summed with a nonneg core `W z ≥ 0` (`> 0` a.e.), integrated over a finite-volume outer domain `Z`,
is finite ABOVE the block threshold `(m+1)/2` provided the core integral at the SHIFTED exponent
`c' − (m+1)/2` is finite. Per-`z` the banked `radial_morse_residual_power_le` peels the Morse block
(charge `(m+1)/2`), leaving `Cresid · (W z)^{−(c'−(m+1)/2)}`; `lintegral_mono_ae` (using the a.e.
positivity `hWpos`) + `lintegral_const_mul'` pull out the finite constant, and `hcore` (the reduced
core finiteness — the strong IH in the front-peel application) closes it. This is the "sum-not-min"
additive composition: the block charge `(m+1)/2` and the core budget ADD, not min. The complementary
regime `c' < (m+1)/2` is the banked `radial_morse_dominates_absZ_lt_top` (no core needed); the
measure-zero boundary `c' = (m+1)/2` is out of scope of both. -/
theorem morseCore_residual_lt_top {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (m : ℕ)
    (c' : ℝ) (hc' : (m + 1 : ℝ) / 2 < c') (T : ℝ) (hT : 0 < T)
    (W : Ω → ℝ) (Z : Set Ω) (hWpos : ∀ᵐ z ∂μ.restrict Z, 0 < W z)
    (hcore : ∫⁻ z in Z, ENNReal.ofReal ((W z) ^ (-(c' - (m + 1 : ℝ) / 2))) ∂μ < ⊤) :
    ∫⁻ z in Z, (∫⁻ P in morseBox (m + 1) T,
        ENNReal.ofReal ((∑ i, (P i) ^ 2 + W z) ^ (-c')) ∂volume) ∂μ < ⊤ := by
  calc ∫⁻ z in Z, (∫⁻ P in morseBox (m + 1) T,
          ENNReal.ofReal ((∑ i, (P i) ^ 2 + W z) ^ (-c')) ∂volume) ∂μ
      ≤ ∫⁻ z in Z, ENNReal.ofReal (Cresid (m + 1) c') *
          ENNReal.ofReal ((W z) ^ (-(c' - (m + 1 : ℝ) / 2))) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hWpos] with z hz
        calc (∫⁻ P in morseBox (m + 1) T,
                ENNReal.ofReal ((∑ i, (P i) ^ 2 + W z) ^ (-c')) ∂volume)
            ≤ ENNReal.ofReal (Cresid (m + 1) c' * (W z) ^ (-(c' - (m + 1 : ℝ) / 2))) :=
              radial_morse_residual_power_le m c' hc' T hT (W z) hz
          _ = ENNReal.ofReal (Cresid (m + 1) c') *
                ENNReal.ofReal ((W z) ^ (-(c' - (m + 1 : ℝ) / 2))) :=
              ENNReal.ofReal_mul (Cresid_nonneg _ _)
    _ = ENNReal.ofReal (Cresid (m + 1) c') *
          ∫⁻ z in Z, ENNReal.ofReal ((W z) ^ (-(c' - (m + 1 : ℝ) / 2))) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hcore

/-! ## The reduced-Morse-box endpoint (regime dispatch, PROVED modulo the borderline) -/

/-- **The reduced-chain box with an isotropic Morse block is finite below the shifted threshold
(PROVED — regime A/B dispatch, borderline isolated).** For a chain `R` with box finiteness `hIH`, a
`d`-dimensional isotropic Morse block `X` summed with the reduced-chain squared loss
`frobSq (prod R Y)`, integrated over `Y ∈ paramsBoxM R 1` and `X ∈ morseBox d 1`, is finite whenever
`c' < ½·(d + minAdm R)` — the Codex "entry-point" endpoint. Three cases:
* `d = 0` (no Morse block): the integrand is `frobSq(prod R Y)^{−c'}`, pulled out of the trivial
  `X`-integral (`setLIntegral_const`, `morseBox` finite volume), leaving `routeMLayerBoxIntegral R c' 1`,
  finite by `hIH` (`c' < ½·minAdm R`).
* `c' < d/2` (regime B): the banked `radial_morse_dominates_absZ_lt_top` — the Morse block dominates,
  `W ≥ 0`, `paramsBoxM R 1` finite volume; no core, no nondegeneracy needed.
* `c' > d/2` (regime A): the banked `morseCore_residual_lt_top` peels the Morse block (charge `d/2`),
  leaving the reduced core at the shifted exponent `c' − d/2 < ½·minAdm R`, finite by `hIH`; the a.e.
  positivity `hWpos` (supplied only under the regime-A premise `d/2 < c'`, so honest even where the
  reduced chain degenerates and regime A never fires).

The borderline `c' = d/2` (the log endpoint, Codex restatement flag 1) is out of scope of both regime
bricks; isolated as a NAMED sorry. -/
theorem morse_reduced_box_lt_top (R : Fin (L + 1 + 1) → ℕ) (d : ℕ) (c' : NNReal)
    (hIH : RouteMBoxThresholdFinite R)
    (hc : (c' : ℝ) < ((d : ℝ) + (minAdm R : ℝ)) / 2)
    (hWpos : (d : ℝ) / 2 < (c' : ℝ) →
      ∀ᵐ Y ∂(volume.restrict (paramsBoxM R 1)), 0 < frobSq (prod R Y)) :
    ∫⁻ Y in paramsBoxM R 1, (∫⁻ X in morseBox d 1,
        ENNReal.ofReal ((∑ i, (X i) ^ 2 + frobSq (prod R Y)) ^ (-(c' : ℝ))) ∂volume) ∂volume < ⊤ := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- d = 0: the Morse block is empty; pull the constant `X`-integral out, close by `hIH`.
    subst hd0
    have hc0 : (c' : ℝ) < (minAdm R : ℝ) / 2 := by
      rw [Nat.cast_zero, zero_add] at hc; exact hc
    have hinner : ∀ Y : Params R,
        (∫⁻ X in morseBox 0 1, ENNReal.ofReal ((∑ i, (X i) ^ 2 + frobSq (prod R Y)) ^ (-(c' : ℝ)))
            ∂volume)
          = ENNReal.ofReal ((frobSq (prod R Y)) ^ (-(c' : ℝ))) * volume (morseBox 0 1) := by
      intro Y
      rw [← setLIntegral_const (morseBox 0 1)
        (ENNReal.ofReal ((frobSq (prod R Y)) ^ (-(c' : ℝ))))]
      refine setLIntegral_congr_fun (morseBox_measurableSet 0 1) (fun X _ => ?_)
      simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    calc ∫⁻ Y in paramsBoxM R 1, (∫⁻ X in morseBox 0 1,
            ENNReal.ofReal ((∑ i, (X i) ^ 2 + frobSq (prod R Y)) ^ (-(c' : ℝ))) ∂volume) ∂volume
        = ∫⁻ Y in paramsBoxM R 1,
            ENNReal.ofReal ((frobSq (prod R Y)) ^ (-(c' : ℝ))) * volume (morseBox 0 1) ∂volume := by
          exact lintegral_congr_ae (Filter.Eventually.of_forall (fun Y => hinner Y))
      _ = (∫⁻ Y in paramsBoxM R 1, ENNReal.ofReal ((frobSq (prod R Y)) ^ (-(c' : ℝ))) ∂volume)
            * volume (morseBox 0 1) := by
          rw [lintegral_mul_const' _ _ (morseBox_volume_lt_top 0 1).ne]
      _ < ⊤ := ENNReal.mul_lt_top (hIH c' hc0) (morseBox_volume_lt_top 0 1)
  · -- d = m + 1.
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hdpos.ne'
    rcases lt_trichotomy (c' : ℝ) ((m + 1 : ℝ) / 2) with hlt | heq | hgt
    · -- regime B: the Morse block dominates (banked).
      have := radial_morse_dominates_absZ_lt_top (m := m) (volume) (c' : ℝ) hlt c'.coe_nonneg
        1 one_pos (fun Y => frobSq (prod R Y)) (fun Y => frobSq_nonneg _)
        (paramsBoxM R 1) (paramsBoxM_volume_lt_top R 1)
      exact this
    · -- borderline c' = (m+1)/2: the log endpoint (Codex flag 1), out of scope of both bricks.
      sorry
    · -- regime A: peel the Morse block (banked `morseCore_residual_lt_top`), close the core by `hIH`.
      have hshift : (c' : ℝ) - ((m : ℝ) + 1) / 2 < (minAdm R : ℝ) / 2 := by
        have hh : ((↑(m + 1) : ℝ) + (minAdm R : ℝ)) / 2
            = ((m : ℝ) + 1) / 2 + (minAdm R : ℝ) / 2 := by push_cast; ring
        rw [hh] at hc; linarith
      have hpos : (0 : ℝ) ≤ (c' : ℝ) - ((m : ℝ) + 1) / 2 := by linarith
      set c'' : NNReal := ⟨(c' : ℝ) - ((m : ℝ) + 1) / 2, hpos⟩ with hc''
      have hc''val : (c'' : ℝ) = (c' : ℝ) - ((m : ℝ) + 1) / 2 := rfl
      have hcore : ∫⁻ Y in paramsBoxM R 1,
          ENNReal.ofReal ((frobSq (prod R Y)) ^ (-((c' : ℝ) - ((m : ℝ) + 1) / 2))) ∂volume < ⊤ := by
        have hlt2 : (c'' : ℝ) < (minAdm R : ℝ) / 2 := by rw [hc''val]; exact hshift
        have hfin := hIH c'' hlt2
        unfold routeMLayerBoxIntegral at hfin
        rw [hc''val] at hfin
        exact hfin
      have hWp : ∀ᵐ Y ∂(volume.restrict (paramsBoxM R 1)), 0 < frobSq (prod R Y) := by
        apply hWpos
        show ((↑(m + 1) : ℝ)) / 2 < (c' : ℝ)
        push_cast; exact hgt
      exact morseCore_residual_lt_top (μ := volume) m (c' : ℝ) hgt 1 one_pos
        (fun Y => frobSq (prod R Y)) (paramsBoxM R 1) hWp hcore

/-- **A chain with a zero width has `minAdm = 0`.** If some width `R i = 0`, the layer-peel recursion
`minAdmRec` bottoms out at `0`: the pivot cut `t = min(R₀,R₁)` zeroes the leading block
`(R₀−t)(R₁−t) = 0`, and the reduced chain `redChain t R` still carries a zero width (the original one,
or `t = 0` when the zero sat in the leading pair), so the residual `minAdmRec (redChain t R)` is `0` by
induction on arity. Used for the degenerate front-peel branch `q = tailMin M` (a tail width reduces to
`0`), where the reduced-chain codim vanishes and the front Morse block alone charges. -/
private theorem minAdmRec_eq_zero_of_width_zero :
    ∀ {K : ℕ} (R : Fin (K + 1) → ℕ), (∃ i, R i = 0) → minAdmRec R = 0
  | 0, _, _ => rfl
  | 1, R, ⟨i, hi⟩ => by
      rw [minAdmRec_leaf]; fin_cases i <;> simp_all
  | (l + 1 + 1), R, ⟨i, hi⟩ => by
      rw [minAdmRec_succ_succ]
      apply Nat.le_zero.mp
      refine le_trans (Finset.inf'_le _
        (show min (R 0) (R 1) ∈ Finset.range (min (R 0) (R 1) + 1) from by
          rw [Finset.mem_range]; omega)) ?_
      have hblock : (R 0 - min (R 0) (R 1)) * (R 1 - min (R 0) (R 1)) = 0 := by
        rcases le_total (R 0) (R 1) with h | h
        · rw [min_eq_left h, Nat.sub_self, Nat.zero_mul]
        · rw [min_eq_right h, Nat.sub_self, Nat.mul_zero]
      rw [hblock, Nat.zero_add]
      refine Nat.le_of_eq (minAdmRec_eq_zero_of_width_zero (redChain (min (R 0) (R 1)) R) ?_)
      -- the reduced chain still carries a zero width.
      by_cases ht0 : min (R 0) (R 1) = 0
      · exact ⟨0, by rw [redChain_zero]; exact ht0⟩
      · -- `t ≠ 0` ⟹ `R 0, R 1 ≥ 1`, so the zero index sits at position `≥ 2`, surviving `redChain`.
        have hR0 : R 0 ≠ 0 := fun h => ht0 (by rw [h, Nat.zero_min])
        have hR1 : R 1 ≠ 0 := fun h => ht0 (by rw [h, Nat.min_zero])
        revert hi
        refine Fin.cases ?_ (fun i' => ?_) i
        · intro hi; exact absurd hi hR0
        · refine Fin.cases ?_ (fun j => ?_) i'
          · intro hi; rw [Fin.succ_zero_eq_one] at hi; exact absurd hi hR1
          · intro hi; exact ⟨j.succ, by rw [redChain_succ]; exact hi⟩

/-- **The reduced chain is a.e.-nonvanishing on the regime-A stratum (NAMED SORRY — CRUX A).** Under
the regime-A premise `M₀q/2 < c'` (with `c' < ½·minAdm M`), the reduced chain `redTail M q` is
nondegenerate: `M₀q < minAdm M ≤ frontCharge q = M₀q + minAdm (redTail M q)` forces
`minAdm (redTail M q) > 0`, so every tail width `> q` and the reduced product `prod (redTail M q) Y`
is a genuine (not identically-zero) polynomial in `Y`, hence nonzero a.e. on the box (nonzero real
polynomial ⟹ null zero-set; `_ae_pos` template `Uval4422_ae_pos`). The premise gate makes the
statement honest where the reduced chain degenerates (`q = tailMin M`): there `M₀q/2 = ½·frontCharge ≥
½·minAdm M > c'`, so regime A never fires and the implication is vacuous. -/
theorem reduced_frobSq_ae_pos (M : Fin (L + 1 + 1 + 1) → ℕ) (q : ℕ) (hq : q ≤ tailMin M)
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    ((M 0 * q : ℕ) : ℝ) / 2 < (c' : ℝ) →
      ∀ᵐ Y ∂(volume.restrict (paramsBoxM (fun i : Fin (L + 1 + 1) => M i.succ - q) 1)),
        0 < frobSq (prod (fun i : Fin (L + 1 + 1) => M i.succ - q) Y) := by
  intro hreg
  set R : Fin (L + 1 + 1) → ℕ := fun i : Fin (L + 1 + 1) => M i.succ - q with hR
  by_cases hall : ∀ i, 1 ≤ R i
  · -- All reduced widths `≥ 1`: the reduced product is a genuine nonzero polynomial in `Y`, so
    -- `frobSq (prod R Y) > 0` a.e. (nonzero real polynomial ⟹ null zero-set), via `corePoly`.
    apply ae_restrict_of_ae
    have hne : corePoly R ≠ 0 := by
      obtain ⟨A, hA⟩ := dlnLoss_deepest_core_ne_zero_witness R hall
      intro hP0
      apply hA
      have hev := eval_corePoly R ((paramsEquivFlat R) A)
      rw [hP0] at hev
      simpa using hev.symm
    have hae : ∀ᵐ z : Fin (flatDim R) → ℝ, MvPolynomial.eval z (corePoly R) ≠ 0 :=
      MvPolynomial.ae_eval_ne_zero (corePoly R) hne
    have hmp := measurePreserving_paramsEquivFlat R
    have hmeas : MeasurableSet {z : Fin (flatDim R) → ℝ | MvPolynomial.eval z (corePoly R) ≠ 0} :=
      (MvPolynomial.measurableSet_zeroSet (corePoly R)).compl
    have haeParams : ∀ᵐ Y : Params R,
        MvPolynomial.eval (paramsEquivFlat R Y) (corePoly R) ≠ 0 := by
      rw [← hmp.map_eq] at hae
      exact (ae_map_iff hmp.measurable.aemeasurable hmeas).1 hae
    refine haeParams.mono (fun Y hY => ?_)
    have hfe : MvPolynomial.eval (paramsEquivFlat R Y) (corePoly R) = frobSq (prod R Y) := by
      rw [eval_corePoly R (paramsEquivFlat R Y), MeasurableEquiv.symm_apply_apply,
        dlnLoss_zero_eq_frobSq]
    rw [hfe] at hY
    exact lt_of_le_of_ne (frobSq_nonneg _) (Ne.symm hY)
  · -- Some reduced width is `0` (forces `q = tailMin M`): `minAdm R = 0`, so the regime-A premise
    -- `M₀q/2 < c'` contradicts `c' < ½·minAdm M ≤ M₀q/2` — the statement is vacuously true.
    exfalso
    push_neg at hall
    obtain ⟨i₀, hi₀⟩ := hall
    have hzero : ∃ i, R i = 0 := ⟨i₀, by omega⟩
    have hminR : minAdm R = 0 := by
      rw [← minAdmRec_eq_minAdm]; exact minAdmRec_eq_zero_of_width_zero R hzero
    have hminLam : minAdm (fun i : Fin (L + 1 + 1) => M i.succ - q) = 0 := by
      rw [hR] at hminR; exact hminR
    have hfc := frontCharge_ge_minAdm M q hq
    unfold frontCharge at hfc
    rw [hminLam] at hfc
    have hfc2 : minAdm M ≤ M 0 * q := by omega
    have hcast : (minAdm M : ℝ) ≤ ((M 0 * q : ℕ) : ℝ) := by exact_mod_cast hfc2
    linarith

/-- **The reduced-chain Morse-block front integral** — the CoV image of one pivot chart's stratum
contribution: the reduced chain `redTail M q` box integral with the front-peel Morse block of
dimension `M₀·q`. -/
noncomputable def reducedMorseFront (M : Fin (L + 1 + 1 + 1) → ℕ) (q : ℕ) (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ Y in paramsBoxM (fun i : Fin (L + 1 + 1) => M i.succ - q) 1,
    (∫⁻ X in morseBox (M 0 * q) 1,
      ENNReal.ofReal ((∑ i, (X i) ^ 2
        + frobSq (prod (fun i : Fin (L + 1 + 1) => M i.succ - q) Y)) ^ (-c')) ∂volume) ∂volume

/-- **The reduced-Morse front integral is finite below the geometric threshold (PROVED, radius 1).**
For `q ≤ tailMin M` and `c' < ½·minAdm M`, `reducedMorseFront M q c' < ⊤`, given the reduced-chain box
finiteness `hIH`. Immediate from `morse_reduced_box_lt_top` (regime dispatch) at `R = redTail M q`,
`d = M₀q`: the threshold `c' < ½·(M₀q + minAdm (redTail M q))` follows from `frontCharge_ge_minAdm`
(`minAdm M ≤ M₀q + minAdm (redTail M q)`); the regime-A nondegeneracy is `reduced_frobSq_ae_pos`.
This is the CoV image endpoint the datum constructor consumes; the radius-`1` box here is the core case
— the threaded shear enlarges the reduced box (the coefficients `K_i = γ_i α_i⁻¹` are unbounded on the
chart), so the constructor additionally needs the enlarged-radius domination (Codex flag 2, deferred). -/
theorem reducedMorseFront_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ) (q : ℕ) (hq : q ≤ tailMin M)
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (hIH : RouteMBoxThresholdFinite (fun i : Fin (L + 1 + 1) => M i.succ - q)) :
    reducedMorseFront M q (c' : ℝ) < ⊤ := by
  unfold reducedMorseFront
  refine morse_reduced_box_lt_top (fun i : Fin (L + 1 + 1) => M i.succ - q) (M 0 * q) c' hIH ?_ ?_
  · have hfc := frontCharge_ge_minAdm M q hq
    unfold frontCharge at hfc
    have hcast : (minAdm M : ℝ)
        ≤ ((M 0 * q : ℕ) : ℝ) + ((minAdm (fun i : Fin (L + 1 + 1) => M i.succ - q) : ℕ) : ℝ) := by
      exact_mod_cast hfc
    linarith
  · exact reduced_frobSq_ae_pos M q hq c' hc'

/-! ## The normal-slice chart datum — the interface (route A) + the assembly (route B)

The crux is decomposed via the `NormalSliceChartData` interface pattern (Codex decomp
`threads/genm-fpcarrier/codex/normalslice-decomp-answer.md`, §4 "cleanest decomposition"): the
analytic assembly `normalSlice_transfer` reduces to a finite chart family whose per-chart finiteness
is the interface field, so the only remaining content is the geometric construction of the datum
(the threaded shear + loss split + finite pivot-chart cover, in the constructor). -/

/-- **The normal-slice chart datum.** An abstract finite-chart witness that the tail-rank-`q` stratum
contribution `frontStratumIntegral M q c'` reduces to a finite family of chart contributions, each
finite below the geometric threshold `½·minAdm M` given the reduced-chain box finiteness (the strong
induction hypothesis `RouteMBoxThresholdFinite (redTail M q)`).

Constructing a `NormalSliceChartData M q` is exactly the threaded normal-slice change of variables
(vslice `normalslice-cert.md` §2–4): the finite pivot-chart cover of the tail (`ι`), on each of which
the block-shear CoV `M_1·P = [[α,B],[0,Z]]` (`α` invertible, `Z = prod (redTail M q) Y` the reduced
product) turns the chart contribution into the disjoint Morse-block-plus-reduced-core integral
`∫ ∫ (‖R‖² + frobSq Z)^{−c'}`, finite by the two banked radial-Morse endpoints (`morseCore_residual_lt_top`
regime A + `radial_morse_dominates_absZ_lt_top` regime B) fed by the strong IH at the shifted exponent
(`shiftedThreshold`). -/
structure NormalSliceChartData (M : Fin (L + 1 + 1 + 1) → ℕ) (q : ℕ) where
  /-- The finite chart index (a pivot-chart selection of the tail). -/
  ι : Type
  /-- The chart index is finite. -/
  [fintypeι : Fintype ι]
  /-- The chart contribution to the stratum integral, at exponent `c'`. -/
  chartInt : ι → ℝ → ℝ≥0∞
  /-- The stratum contribution is dominated by the finite chart sum (the pivot-chart cover +
  threaded-shear CoV, subadditive over the finite cover). -/
  cover : ∀ c' : ℝ, frontStratumIntegral M q c' ≤ ∑ i, chartInt i c'
  /-- Each chart contribution is finite below the geometric threshold, given the reduced-chain box
  finiteness (the strong IH). Bundles the loss split + the regime-A/B radial-Morse endpoints. -/
  chartFinite : ∀ c' : NNReal, (c' : ℝ) < (minAdm M : ℝ) / 2 →
      RouteMBoxThresholdFinite (fun i : Fin (L + 1 + 1) => M i.succ - q) →
      ∀ i : ι, chartInt i (c' : ℝ) < ⊤

attribute [instance] NormalSliceChartData.fintypeι

/-- **The normal-slice transfer FROM the chart datum (route B, PROVED).** Given a
`NormalSliceChartData M q`, the stratum contribution is finite: the finite chart cover dominates it
(`cover`) and each chart is finite (`chartFinite`); a finite sum of finite terms is finite
(`ENNReal.sum_lt_top`). The analytic assembly — no geometry — modulo the datum being inhabited. -/
theorem normalSlice_transfer_of_data (M : Fin (L + 1 + 1 + 1) → ℕ) (q : ℕ)
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (hIH : RouteMBoxThresholdFinite (fun i : Fin (L + 1 + 1) => M i.succ - q))
    (χ : NormalSliceChartData M q) :
    frontStratumIntegral M q (c' : ℝ) < ⊤ :=
  lt_of_le_of_lt (χ.cover (c' : ℝ))
    (ENNReal.sum_lt_top.mpr (fun i _ => χ.chartFinite c' hc' hIH i))

/-- **The normal-slice chart datum EXISTS (the geometric construction, NAMED SORRY).** For an
admissible tail-rank `q ≤ tailMin M`, the tail-rank-`q` stratum admits a normal-slice chart datum. This
is the threaded normal-slice change of variables of vslice `normalslice-cert.md` §2–4 — the sole
remaining geometric content of the front-peel: the finite pivot-chart cover of `{rank P ≥ q}`
(`pivotLocus_eq_iUnion`), the opaque-width block-shear identity `M_i·X_i·M_{i+1}⁻¹ = [[α_i,B_i],[0,Y_i]]`
(`L = 2` base banked as `frobSq_schur_block_split`; the rank output is banked as
`RouteMSJThreadedShear.rank_eq_q_add_of_normalForm`), its measure-preservation (Jacobian `±1`), and the
disjoint loss split `frobSq(A₀·P) ≃ ‖R‖² + frobSq (prod (redTail M q) Y)`. Isolated as the single
geometric obligation; the analytic assembly above (`normalSlice_transfer_of_data`) and the reduced-Morse
endpoints (`morseCore_residual_lt_top`, banked `radial_morse_dominates_absZ_lt_top`) are proven. -/
noncomputable def normalSliceChartData (M : Fin (L + 1 + 1 + 1) → ℕ) (q : ℕ) (hq : q ≤ tailMin M) :
    NormalSliceChartData M q :=
  sorry

/-! ## THE CRUX — the normal-slice transfer (named sorry, vslice-fed) -/

/-- **THE NAMED CRUX — the front-peel step on one tail-rank stratum.** On the stratum `{rank P = q}`
(`P = prod (tailChain M) A'`), the contribution `frontStratumIntegral M q c'` is finite, GIVEN
box-finiteness of the SHIFTED chain `(fun i => M i.succ − q)` (the strong induction hypothesis) and
the threshold `c' < ½·minAdm M`.

Proof route — the width-general threaded normal-slice CoV (vslice `normalslice-cert.md`, #109,
Codex-decorrelated; decomposition validated in `codex/normalslice-decomp-answer.md`). The remaining
work is the opaque-width CoV construction; the analytic endpoints are banked/proven:
* **The threaded shear CoV (the two HARD opaque-width walls).** Block each tail factor
  `X_i = [[A_i,B_i],[C_i,D_i]]` (`A_i` `q×q`); thread right-to-left (`K_L=0`, `α_i=A_i+B_i K_{i+1}`,
  `K_i=γ_i α_i⁻¹`, `Y_i=D_i−γ_i α_i⁻¹ B_i`). The block-shear identity
  `M_i·X_i·M_{i+1}⁻¹ = [[α_i,B_i],[0,Y_i]]` (unit-triangular `M_i`, det 1) telescopes to
  `rank P = q + rank(Y₁···Y_{L-1})`, so `{rank P ≤ q} ⟺ {prod (redTail M q) = 0}` and the reduced
  product is the `prod` of the reduced chain `redTail M q = fun i => M i.succ − q`. `L=2` is banked
  (`frobSq_schur_block_split`); the opaque-width lift + the threaded shear's measure-preservation
  (Jacobian `±1`, `α_i⁻¹` only as unit coefficients — det-inverse compass holds) are the new bricks.
* **The additive endpoint (PROVED here + banked).** After the CoV the loss is `‖R‖² + ‖Z‖²`
  (disjoint blocks: `R` the `M₀·q` Morse block from `A₀`, `Z = prod (redTail M q)` reduced core),
  so the charges ADD ("sum-not-min"). Regime A (`c' > M₀q/2`): `morseCore_residual_lt_top` (above)
  peels the Morse block to the reduced-core integral at exponent `c'−M₀q/2`, finite by `hIH`. Regime
  B (`c' < M₀q/2`): banked `radial_morse_dominates_absZ_lt_top`. The `hWpos` a.e.-positivity is
  CRUX A (nondegenerate reduced chain ⟹ `prod (redTail M q) ≠ 0` a.e.; `_ae_pos` template).
* **Close by the IH.** `shiftedThreshold` (proven) gives `c' − M₀·q/2 < ½·minAdm (redTail M q)`, so
  the `hIH` box at the shifted exponent (a `NNReal` in regime A) is finite; the finite pivot-chart
  cover over `α_i`-invertibility charts (`pivotLocus_eq_iUnion` + `pivotChartCover_matBox_le_sum`)
  assembles the strata. Boundary `c' = M₀q/2` is the one measure-zero edge (log endpoint). -/
theorem normalSlice_transfer (M : Fin (L + 1 + 1 + 1) → ℕ) (q : ℕ) (hq : q ≤ tailMin M)
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (hIH : RouteMBoxThresholdFinite (fun i : Fin (L + 1 + 1) => M i.succ - q)) :
    frontStratumIntegral M q (c' : ℝ) < ⊤ :=
  normalSlice_transfer_of_data M q c' hc' hIH (normalSliceChartData M q hq)

/-! ## The front-peel inductive step + the W1 assembly -/

/-- **The front-peel inductive STEP (`SJStepHyp`).** For a `≥ 3`-width chain `M`, GIVEN
box-finiteness of every one-arity-shorter chain (the strong IH), box-finiteness holds for `M`. The
front-split box integral is covered by the finite tail-rank stratification (`outerRankCover`); each
stratum contribution is finite by the normal-slice transfer (`normalSlice_transfer`), whose shifted
chain `(fun i => M i.succ − q)` is supplied to the IH; a finite sum of finite terms is finite. An
alternative to `sjResolutionStep_proof` routing through the front-peel `A₀ ↦ A₀·U` rather than the
pivot–Schur peel; it consumes ONLY the IH (no `sjJointResolution`), so W1 is non-circular. -/
theorem frontPeelStep_proof : SJStepHyp := by
  intro L M hIH c' hc'
  refine lt_of_le_of_lt (outerRankCover M (c' : ℝ)) ?_
  refine ENNReal.sum_lt_top.mpr (fun q hq => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hq
  exact normalSlice_transfer M q hq c' hc' (hIH (fun i : Fin (L + 1 + 1) => M i.succ - q))

/-- **The general-`L` box-finiteness `RouteMBoxThresholdFinite M`, ∀M (wiring W1).** The banked
axiom-clean arity strong-induction wrapper `routeMBoxThresholdFinite_of_step`, applied to the
front-peel step (`frontPeelStep_proof`) and the banked `L = 1` Morse base (`sjBase1_freeMatrix`).
Discharges the `(□)` that is the sole analytic hypothesis of `aoyagi_learning_coefficient_gen`. -/
theorem routeMBoxThresholdFinite_frontPeel :
    ∀ {L : ℕ} (M : Fin (L + 1) → ℕ), RouteMBoxThresholdFinite M :=
  routeMBoxThresholdFinite_of_step frontPeelStep_proof sjBase1_freeMatrix

/-- **The canonical joint resolution, closed as a front-peel corollary (wiring W1).** The exact
statement of the canonical open leaf `sjJointResolution` (`RouteMSJResolution.lean:803`), re-proved
via the banked reduction `sjJointResolution_of_boxThresholdFinite` applied to the INDEPENDENT
front-peel box-finiteness `routeMBoxThresholdFinite_frontPeel M`. Valid precisely because the
box-finiteness is proven by the front-peel recursion, NOT through the spine (the circularity the
joint-reduce header flags). The unused hypotheses (`_hIH`, `_ht`, `_ht2`) are kept to make this a
literal drop-in for the canonical signature — the controller wires this to discharge the `:803`. -/
theorem sjJointResolution_frontPeel (M : Fin (L + 1 + 1 + 1) → ℕ)
    (_hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (t : ℕ) (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1))
    (_ht : 1 ≤ t) (_ht2 : t ≤ min (M 0) (M 1)) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    gammaPeelIntegral M t ρ κ (c' : ℝ) < ⊤ :=
  sjJointResolution_of_boxThresholdFinite M (routeMBoxThresholdFinite_frontPeel M) t ρ κ c' hc'

end DLNFibre.DLN.RLCT
