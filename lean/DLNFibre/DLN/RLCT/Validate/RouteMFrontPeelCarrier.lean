import DLNFibre.DLN.RLCT.Validate.RouteMSJJointReduce
import DLNFibre.DLN.RLCT.Validate.RouteMFrontPeelCharge

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
* `outerRankCover` — NAMED SORRY (measure cover; correct statement). The front-split box integral is
  bounded by the finite sum over `q = 0..tailMin M` of the stratum contributions.
* `normalSlice_transfer` — **THE NAMED CRUX** (SORRY). On the `{rank P = q}` stratum, the
  contribution is finite given box-finiteness of the SHIFTED chain (the IH). Bundles: the
  `A₀ ↦ A₀·U` shift (regimes A/B), the normal-slice iso to the shifted `Σ⁰`, and the IH at the
  shifted exponent.
  Decomposes into CRUX B (the "sum-not-min" corner blow-up, mostly banked radial/sum machinery) and
  CRUX A (bounded-below cores) — see the thread tide-plan.
* `frontPeelStep_proof : SJStepHyp` — PROVED (modulo the two named sorries), composing
  `outerRankCover` + `normalSlice_transfer`. The front-peel inductive step.
* `routeMBoxThresholdFinite_frontPeel` — PROVED (modulo the sorries): `RouteMBoxThresholdFinite M`
  ∀M, via `routeMBoxThresholdFinite_of_step frontPeelStep_proof sjBase1_freeMatrix`.
* `sjJointResolution_frontPeel` — PROVED (modulo the sorries): the canonical `sjJointResolution`
  statement, re-proved via `sjJointResolution_of_boxThresholdFinite` applied to the INDEPENDENT
  front-peel box-finiteness (NOT through the spine — circular, per `RouteMSJJointReduce`'s header).
  The drop-in the controller wires to discharge the canonical `RouteMSJResolution.lean:803` sorry.

**Branch discipline.** All gaps live on branch `genm-fpcarrier`; canonical stays 0-sorry/0-axiom.
The two `sorry`s are `outerRankCover` (routine measure theory) and `normalSlice_transfer` (the
single genuine analytic crux, vslice-fed).
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

/-! ## The front-peel cover (named sorry — routine measure theory) -/

/-- **The front-split box integral is covered by the finite tail-rank stratification.** For every
`c'`, `routeMLayerBoxIntegral M c' 1 ≤ ∑_{q=0}^{tailMin M} frontStratumIntegral M q c'`. Route:
rewrite via the banked `routeMLayerBoxIntegral_front_split` to the tail-outer front-factor integral;
the outer tail box partitions as `⋃_{q ≤ tailMin M} {rank(prod (tailChain M) A') = q}` (the tail
product has rank `≤ tailMin M` everywhere), a finite cover; subadditivity of the lintegral over the
finite union collapses to the `Finset.range (tailMin M + 1)` sum. Pure measure theory (mirrors
`pivotChartCover_lintegral_le_sum`). -/
theorem outerRankCover (M : Fin (L + 1 + 1 + 1) → ℕ) (c' : ℝ) :
    routeMLayerBoxIntegral M c' 1
      ≤ ∑ q ∈ Finset.range (tailMin M + 1), frontStratumIntegral M q c' := by
  sorry

/-! ## THE CRUX — the normal-slice transfer (named sorry, vslice-fed) -/

/-- **THE NAMED CRUX — the front-peel step on one tail-rank stratum.** On the stratum `{rank P = q}`
(`P = prod (tailChain M) A'`), the contribution `frontStratumIntegral M q c'` is finite, GIVEN
box-finiteness of the SHIFTED chain `(fun i => M i.succ − q)` (the strong induction hypothesis) and
the threshold `c' < ½·minAdm M`.

Proof route (the single genuine analytic risk; vslice `(3,3,3,4)`-fed, then opaque-width lifted):
* **The `A₀ ↦ A₀·U` shift.** Write `P = U·V` on `{rank P = q}`; `frobSq(A₀·P) = frobSq((A₀·U)·V)`
  and `A₀ ↦ A₀·U` surjects onto `M₀ × q` (kernel dim `M₀·(M₁−q)`), an isotropic `M₀·q` Morse block
  plus a bounded kernel box. Regime B (`c' < M₀·q/2`): finite directly. Regime A (`c' > M₀·q/2`):
  shift the exponent to `c' − M₀·q/2` on the deeper tail-rank locus (banked corank bricks
  `matBox_corank_dominates_absZ_lt_top` / `matBox_corank_residual_absZ_le`, block dim `M₀·q`).
* **The normal-slice iso (paper `addlongest`).** The tail-rank locus `{rank P ≤ q}` has the same
  singularity type as `Σ⁰` of the shifted chain, transferring the residual to
  `routeMLayerBoxIntegral (fun i => M i.succ − q) (c' − M₀·q/2) 1`. The "sum-not-min" corner
  composition (CRUX B, banked radial/sum machinery — `sumSqND_box_lt_top`,
  `radial_morse_residual_power_le`, `lintegral_eq_polar`; AVOID the product/min tools) plus
  bounded-below cores (CRUX A, the endpoint `terminal_monomial_mul_unit_lintegral_lt_top` consumes
  them as `hunit`) live here.
* **Close by the IH.** `shiftedThreshold` gives `c' − M₀·q/2 < ½·minAdm (shifted)`, so `hIH` at the
  shifted exponent (a `NNReal` in regime A; regime B is finite unconditionally) finishes. -/
theorem normalSlice_transfer (M : Fin (L + 1 + 1 + 1) → ℕ) (q : ℕ) (hq : q ≤ tailMin M)
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (hIH : RouteMBoxThresholdFinite (fun i : Fin (L + 1 + 1) => M i.succ - q)) :
    frontStratumIntegral M q (c' : ℝ) < ⊤ := by
  sorry

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
