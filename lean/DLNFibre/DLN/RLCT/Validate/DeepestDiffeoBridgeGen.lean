import DLNFibre.DLN.RLCT.Validate.DeepestPsiContDiff
import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridge
import DLNFibre.DLN.RLCT.Validate.DeepestSplitSmooth
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeGen` — the general-`L` conjugate diffeo bridge (#120 `hstep2`, piece 5c)

The general-`L` analog of the L=2 `deepest_diffeo_bridge_L2_impl`. It supplies the CHAIN-INDEPENDENT
analytic core of the `hstep2` close: the **conjugate flat diffeo**
`Psi = split⁻¹ ∘ coreAbsorb⁻¹ ∘ Ψ ∘ coreAbsorb ∘ split` and the reduction of
`rlctAtOn Φscore wstar = rlctAtOn Φcore wstar` to two precisely-named geometric germ hypotheses,
via the banked `rlctAtOn_diffeo_bridge_of`.

## Why the CONJUGATE (mirrors the L=2 `…Conj` machinery)
`coreAbsorb = deepestCoreAbsorb` (the additive Schur shear) turns the raw core `T_s` into the per-layer
Schur core `S_s = T_s − Z_s(1+X_s)⁻¹Y_s`, so `deepestCoreF (coreAbsorb q).2.1 = ‖∏_s S_s‖²`. The
absorbing shear `Ψ = deepestPsiCoreShear K` then acts on the ALREADY-corrected core, `S_s ↦ (1−K_s)·S_s`,
so `deepestCoreF (Ψ (coreAbsorb q)).2.1 = ‖∏_s (1−K_s)·S_s‖²`. To pull this back to `deepestCoreF
(coreAbsorb q).2.1` (the `Φcore` core) while leaving the reg/spectator coordinates alone, the flat diffeo
is the CONJUGATE `g = coreAbsorb⁻¹ ∘ Ψ ∘ coreAbsorb` (through the `split` chart) — the `coreAbsorb⁻¹`
undoes the outer `coreAbsorb` so that `Φcore ∘ (split⁻¹ ∘ g ∘ split)` reads `deepestCoreF (Ψ (coreAbsorb
(split x))).2.1` on the core and `regStraighten` on the reg/spec (both slots fixed by `g`).

## What is banked here (chain-independent, cite-NOTHING pure analysis)
- `hasStrictFDerivAt_coreShearHomeo_zero` — the forward mirror of the banked
  `hasStrictFDerivAt_coreShearHomeo_symm_zero` (`D(coreShearHomeo shift)(0) = id` when `D(shift)(0) = 0`).
- `deepestGConjFlat` — the conjugate flat diffeo; `contDiff_deepestGConjFlat` (ContDiff ⊤ from the banked
  smoothness of `split^±`, `coreAbsorb^±`, `Ψ`), `hasStrictFDerivAt_deepestGConjFlat` (`dPsi(wstar) = id`
  by the chain `deepestSplitCLE⁻¹ ∘ id ∘ id ∘ id ∘ deepestSplitCLE`), `deepestGConjFlat_fixpoint`.
- `deepest_diffeo_bridge_gen_impl` — the reduction of `hstep2` to two germs (`huntwist`, `hreginv`) via
  `rlctAtOn_diffeo_bridge_of`. Mirrors `deepest_diffeo_bridge_L2_impl`; does NOT close the `hstep2` sorry.

## What is DEFERRED to later tides (the coupled geometric BULK, pieces 4 + 5a/5b)
- **Piece 4**: the concrete DLN coupling `K = Kcoup (Cq q) s` (framed chain `Cq`) + `hKcd`/`hK0`. The
  chain choice is TIGHTLY coupled to the readback (decorrelated-Codex flag: the bare `1+gaugeReadX`
  per-layer chain was numerically FALSE for `Score` at L=2 — the actual layer pivots `deepBlkA_s +
  gaugeReadX_s` entered; the endpoint frames `P0,QL` are removed by `schur_frame_transform` but the
  `deepBlk` constants are NOT). So `K` must be built from the SAME chain piece 5 proves equals `Score`.
- **Piece 5a** (`huntwist`): `deepestCoreF (Ψ (coreAbsorb (split x))).2.1 = Score x` — `schur_product_ldu_rec`
  on the framed chain + the `Fin (H k)` cast + `rcore_eq_schur_of_corner_split` + `schur_frame_transform`.
- **Piece 5b** (`hreginv`): `(regStraighten (coreAbsorb⁻¹ (Ψ (coreAbsorb (split x))))).1 = (regStraighten
  (split x)).1` — the general-`L` E2 reg-preservation (`deepestEFull` reads the core slot at the last
  layer, so this is NOT automatic; it is the analog of L=2's `e2_regPreserve`/`hsub3reg`).
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology Matrix.Norms.Elementwise
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The forward `coreShearHomeo` strict derivative at `0` is the identity** (the mirror of
`hasStrictFDerivAt_coreShearHomeo_symm_zero`). `coreShearHomeo shift q = (q.1, q.2.1 + shift(q.1, q.2.2),
q.2.2)`; with `D(shift)(0) = 0` its strict derivative at `0` is the identity (the addition's
shift-derivative vanishes). Needed for the outer `coreAbsorb` factor of the conjugate flat diffeo. -/
theorem hasStrictFDerivAt_coreShearHomeo_zero {Reg Core Spec : Type*}
    [NormedAddCommGroup Reg] [NormedSpace ℝ Reg]
    [NormedAddCommGroup Core] [NormedSpace ℝ Core]
    [NormedAddCommGroup Spec] [NormedSpace ℝ Spec]
    (shift : Reg × Spec → Core) (hcont : Continuous shift)
    (hshift0 : HasStrictFDerivAt shift (0 : Reg × Spec →L[ℝ] Core) 0) :
    HasStrictFDerivAt (fun q : Reg × (Core × Spec) => coreShearHomeo shift hcont q)
      (ContinuousLinearMap.id ℝ (Reg × (Core × Spec))) 0 := by
  -- `coreShearHomeo shift q = (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2))`.
  have hfst : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => q.1)
      (ContinuousLinearMap.fst ℝ Reg (Core × Spec)) 0 :=
    (ContinuousLinearMap.fst ℝ Reg (Core × Spec)).hasStrictFDerivAt
  have hsnd : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => q.2)
      (ContinuousLinearMap.snd ℝ Reg (Core × Spec)) 0 :=
    (ContinuousLinearMap.snd ℝ Reg (Core × Spec)).hasStrictFDerivAt
  have hcore : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => q.2.1)
      ((ContinuousLinearMap.fst ℝ Core Spec).comp (ContinuousLinearMap.snd ℝ Reg (Core × Spec))) 0 :=
    ((ContinuousLinearMap.fst ℝ Core Spec).hasStrictFDerivAt).comp (x := (0 : Reg × (Core × Spec))) hsnd
  have hspec : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => q.2.2)
      ((ContinuousLinearMap.snd ℝ Core Spec).comp (ContinuousLinearMap.snd ℝ Reg (Core × Spec))) 0 :=
    ((ContinuousLinearMap.snd ℝ Core Spec).hasStrictFDerivAt).comp (x := (0 : Reg × (Core × Spec))) hsnd
  have hrs : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => (q.1, q.2.2))
      ((ContinuousLinearMap.fst ℝ Reg (Core × Spec)).prod
        ((ContinuousLinearMap.snd ℝ Core Spec).comp
          (ContinuousLinearMap.snd ℝ Reg (Core × Spec)))) 0 :=
    hfst.prodMk hspec
  have hshiftcomp : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => shift (q.1, q.2.2))
      (0 : Reg × (Core × Spec) →L[ℝ] Core) 0 := by
    have := hshift0.comp (x := (0 : Reg × (Core × Spec))) hrs
    simpa using this
  have hcoreshift : HasStrictFDerivAt
      (fun q : Reg × (Core × Spec) => q.2.1 + shift (q.1, q.2.2))
      ((ContinuousLinearMap.fst ℝ Core Spec).comp (ContinuousLinearMap.snd ℝ Reg (Core × Spec))) 0 := by
    have := hcore.add hshiftcomp
    simpa using this
  have hassemble := hfst.prodMk (hcoreshift.prodMk hspec)
  refine hassemble.congr_fderiv ?_
  ext q <;> simp [ContinuousLinearMap.comp_apply]

/-- **The conjugate flat diffeo** `Psi = split⁻¹ ∘ coreAbsorb⁻¹ ∘ Ψ ∘ coreAbsorb ∘ split` on the flat
parameter space, for a coupling `K`. `split = deepestSplit … wstar`, `coreAbsorb = deepestCoreAbsorb`,
`Ψ = deepestPsiCoreShear K`. Concrete (not abstract over `split`/`coreAbsorb`) so the banked smoothness
facts (`contDiff_deepestSplit`, `contDiff_coreShearHomeo`, …) apply directly. -/
noncomputable def deepestGConjFlat (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (K : DeepestCoupling H r (deepestNGauge H r)) (wstar : Fin (flatDim H) → ℝ) :
    (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ) :=
  fun x => (deepestSplit H r hr hL wstar).symm
    ((deepestCoreAbsorb H r hr hL).symm
      (deepestPsiCoreShear H r (deepestNGauge H r) K
        (deepestCoreAbsorb H r hr hL (deepestSplit H r hr hL wstar x))))

/-- The conjugate flat diffeo is `ContDiff ℝ ⊤` (composition of the five globally-`ContDiff` factors:
`split^±` affine, `coreAbsorb^±` cutoff Schur shears, `Ψ` given `hKcd`). -/
theorem contDiff_deepestGConjFlat (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (K : DeepestCoupling H r (deepestNGauge H r))
    (hKcd : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (fun q => K s q))
    (wstar : Fin (flatDim H) → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (deepestGConjFlat H r hr hL K wstar) := by
  have hsplit : ContDiff ℝ (⊤ : ℕ∞) (deepestSplit H r hr hL wstar) :=
    contDiff_deepestSplit H r hr hL wstar
  have hsplitsymm : ContDiff ℝ (⊤ : ℕ∞) (deepestSplit H r hr hL wstar).symm :=
    contDiff_deepestSplit_symm H r hr hL wstar
  have hca : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) => deepestCoreAbsorb H r hr hL q) := by
    rw [deepestCoreAbsorb]
    exact contDiff_coreShearHomeo (schurCutoffShift H r hr hL)
      (continuous_schurCutoffShift H r hr hL) (contDiff_schurCutoffShift H r hr hL)
  have hcasymm : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) => (deepestCoreAbsorb H r hr hL).symm q) := by
    rw [deepestCoreAbsorb]
    exact contDiff_coreShearHomeo_symm (schurCutoffShift H r hr hL)
      (continuous_schurCutoffShift H r hr hL) (contDiff_schurCutoffShift H r hr hL)
  have hpsi : ContDiff ℝ (⊤ : ℕ∞) (deepestPsiCoreShear H r (deepestNGauge H r) K) :=
    contDiff_deepestPsiCoreShear H r (deepestNGauge H r) K hKcd
  exact hsplitsymm.comp (hcasymm.comp (hpsi.comp (hca.comp hsplit)))

/-- The conjugate flat diffeo has strict Fréchet derivative the identity at `wstar` (the chain
`deepestSplitCLE⁻¹ ∘ id ∘ id ∘ id ∘ deepestSplitCLE = id`, using `dΨ(0) = id`, `d(coreAbsorb^±)(0) = id`,
`d(split)(wstar) = deepestSplitCLE`, and `split wstar = 0`). -/
theorem hasStrictFDerivAt_deepestGConjFlat (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (K : DeepestCoupling H r (deepestNGauge H r))
    (hKcd : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (fun q => K s q))
    (hK0 : ∀ s, K s 0 = 0)
    (wstar : Fin (flatDim H) → ℝ)
    (hbase : deepestSplit H r hr hL wstar wstar = 0) :
    HasStrictFDerivAt (deepestGConjFlat H r hr hL K wstar)
      (ContinuousLinearMap.id ℝ (Fin (flatDim H) → ℝ)) wstar := by
  -- `split` deriv `deepestSplitCLE` at `wstar`.
  have hsplit := hasStrictFDerivAt_deepestSplit H r hr hL wstar wstar
  -- `coreAbsorb` deriv `id` at `split wstar = 0` (forward `coreShearHomeo` mirror).
  have hca0 : HasStrictFDerivAt (fun q : DeepestSplit H r (deepestNGauge H r) =>
      deepestCoreAbsorb H r hr hL q)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r))) 0 := by
    rw [deepestCoreAbsorb]
    exact hasStrictFDerivAt_coreShearHomeo_zero (schurCutoffShift H r hr hL)
      (continuous_schurCutoffShift H r hr hL) (hasStrictFDerivAt_schurCutoffShift_zero H r hr hL)
  have hca : HasStrictFDerivAt (fun q : DeepestSplit H r (deepestNGauge H r) =>
      deepestCoreAbsorb H r hr hL q)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r)))
      (deepestSplit H r hr hL wstar wstar) := by rw [hbase]; exact hca0
  -- `Ψ` deriv `id` at `coreAbsorb (split wstar) = coreAbsorb 0 = 0`.
  have hca_base : deepestCoreAbsorb H r hr hL 0 = 0 := (deepest_coreAbsorb_exists H r hr hL).1
  have hpsi0 : HasStrictFDerivAt (deepestPsiCoreShear H r (deepestNGauge H r) K)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r))) 0 :=
    (deepestPsiCoreShear_isLocalDiffeoAt H r (deepestNGauge H r) K hKcd hK0).2.1
  have hpsi : HasStrictFDerivAt (deepestPsiCoreShear H r (deepestNGauge H r) K)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r)))
      (deepestCoreAbsorb H r hr hL (deepestSplit H r hr hL wstar wstar)) := by
    rw [hbase, hca_base]; exact hpsi0
  -- `coreAbsorb.symm` deriv `id` at `Ψ (coreAbsorb (split wstar)) = 0`.
  have hpsi_base : deepestPsiCoreShear H r (deepestNGauge H r) K 0 = 0 :=
    deepestPsiCoreShear_basepoint H r (deepestNGauge H r) K
  have hcasymm0 : HasStrictFDerivAt (fun q : DeepestSplit H r (deepestNGauge H r) =>
      (deepestCoreAbsorb H r hr hL).symm q)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r))) 0 := by
    rw [deepestCoreAbsorb]
    exact hasStrictFDerivAt_coreShearHomeo_symm_zero (schurCutoffShift H r hr hL)
      (continuous_schurCutoffShift H r hr hL) (hasStrictFDerivAt_schurCutoffShift_zero H r hr hL)
  have hcasymm : HasStrictFDerivAt (fun q : DeepestSplit H r (deepestNGauge H r) =>
      (deepestCoreAbsorb H r hr hL).symm q)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r)))
      (deepestPsiCoreShear H r (deepestNGauge H r) K
        (deepestCoreAbsorb H r hr hL (deepestSplit H r hr hL wstar wstar))) := by
    rw [hbase, hca_base, hpsi_base]; exact hcasymm0
  -- `split.symm` deriv `deepestSplitCLE.symm` at `coreAbsorb.symm (…) = 0`.
  have hca_symm_base : (deepestCoreAbsorb H r hr hL).symm 0 = 0 := by
    conv_lhs => rw [← hca_base]
    rw [(deepestCoreAbsorb H r hr hL).symm_apply_apply]
  have hsplitsymm := hasStrictFDerivAt_deepestSplit_symm H r hr hL wstar
    ((deepestCoreAbsorb H r hr hL).symm
      (deepestPsiCoreShear H r (deepestNGauge H r) K
        (deepestCoreAbsorb H r hr hL (deepestSplit H r hr hL wstar wstar))))
  -- Compose the five factors.
  have hcomp := hsplitsymm.comp wstar
    (hcasymm.comp wstar (hpsi.comp wstar (hca.comp wstar hsplit)))
  refine hcomp.congr_fderiv ?_
  -- The composed derivative simplifies to `id` (`deepestSplitCLE⁻¹ ∘ id∘id∘id ∘ deepestSplitCLE`).
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  exact (deepestSplitCLE H r hr hL).symm_apply_apply w

/-- The conjugate flat diffeo fixes `wstar` (`split wstar = 0`, `coreAbsorb 0 = 0`, `Ψ 0 = 0`,
`coreAbsorb⁻¹ 0 = 0`, `split⁻¹ 0 = wstar`). -/
theorem deepestGConjFlat_fixpoint (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (K : DeepestCoupling H r (deepestNGauge H r)) (wstar : Fin (flatDim H) → ℝ)
    (hbase : deepestSplit H r hr hL wstar wstar = 0) :
    deepestGConjFlat H r hr hL K wstar wstar = wstar := by
  have hca_base : deepestCoreAbsorb H r hr hL 0 = 0 := (deepest_coreAbsorb_exists H r hr hL).1
  have hpsi_base : deepestPsiCoreShear H r (deepestNGauge H r) K 0 = 0 :=
    deepestPsiCoreShear_basepoint H r (deepestNGauge H r) K
  have hca_symm_base : (deepestCoreAbsorb H r hr hL).symm 0 = 0 := by
    conv_lhs => rw [← hca_base]
    rw [(deepestCoreAbsorb H r hr hL).symm_apply_apply]
  rw [deepestGConjFlat, hbase, hca_base, hpsi_base, hca_symm_base, ← hbase,
    (deepestSplit H r hr hL wstar).symm_apply_apply]

/-- **The general-`L` conjugate diffeo bridge** (the reduction of `hstep2` to two geometric germs). Given
the concrete `split = deepestSplit … wstar` (`hsplit_def`) carrying `wstar` to `0` (`hsplit_base`), a
coupling `K` with `hKcd`/`hK0`, and the two germ hypotheses near `wstar`:
* **`huntwist`** — `deepestCoreF (Ψ (coreAbsorb (split x))).2.1 = Score x` (piece 5a, the Schur untwisting);
* **`hreginv`** — `(regStraighten (coreAbsorb⁻¹ (Ψ (coreAbsorb (split x))))).1 = (regStraighten (split
  x)).1` (piece 5b, the reg-preservation of the conjugate),

the two RLCTs agree: `rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`. Proof: the conjugate flat diffeo
`Psi = deepestGConjFlat K` is a local diffeo at `wstar` with `dPsi(wstar) = id`, and the two germs give
`Φcore ∘ Psi =ᶠ[𝓝 wstar] Φscore`, so `rlctAtOn_diffeo_bridge_of` closes it. Mirrors
`deepest_diffeo_bridge_L2_impl`; the two germs are the coupled geometric BULK (pieces 4 + 5a/5b),
NOT closed here. Stated at the weakest hypotheses: any `wstar` whose `split = deepestSplit … wstar`
carries it to `0` (the caller instantiates `wstar = (paramsEquivFlat H) (deepestPoint …)`). -/
theorem deepest_diffeo_bridge_gen_impl (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (K : DeepestCoupling H r (deepestNGauge H r))
    (hKcd : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (fun q => K s q))
    (hK0 : ∀ s, K s 0 = 0)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (Score : (Fin (flatDim H) → ℝ) → ℝ)
    (wstar : Fin (flatDim H) → ℝ)
    (hsplit_def : ⇑split = ⇑(deepestSplit H r hr hL wstar))
    (hsplit_base : split wstar = 0)
    (huntwist : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds wstar,
      deepestCoreF H r (deepestPsiCoreShear H r (deepestNGauge H r) K
        (deepestCoreAbsorb H r hr hL (split x))).2.1 = Score x)
    (hreginv : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds wstar,
      (regStraighten ((deepestCoreAbsorb H r hr hL).symm
        (deepestPsiCoreShear H r (deepestNGauge H r) K
          (deepestCoreAbsorb H r hr hL (split x))))).1
        = (regStraighten (split x)).1)
    (Φscore : (Fin (flatDim H) → ℝ) → ℝ)
    (hΦscore : Φscore = fun x => (∑ i, (regStraighten (split x)).1 i ^ 2) + Score x) :
    rlctAtOn Φscore wstar
      = rlctAtOn
          (fun x : Fin (flatDim H) → ℝ =>
            (∑ i, (regStraighten (split x)).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorb H r hr hL (split x)).2.1)
          wstar := by
  -- The absorbed-core target `Φcore`.
  set Φcore : (Fin (flatDim H) → ℝ) → ℝ :=
    fun x => (∑ i, (regStraighten (split x)).1 i ^ 2)
      + deepestCoreF H r (deepestCoreAbsorb H r hr hL (split x)).2.1 with hΦcore
  -- `split` agrees pointwise with the concrete `deepestSplit … wstar` (`hsplit_def`).
  have hsplit_apply : ∀ y, split y = deepestSplit H r hr hL wstar y := fun y => congrFun hsplit_def y
  -- `split wstar = 0` in the concrete form — feeds the diffeo lemmas' `hbase`.
  have hbase : deepestSplit H r hr hL wstar wstar = 0 := by
    rw [← hsplit_apply wstar]; exact hsplit_base
  -- The conjugate flat diffeo is a local diffeo at `wstar` (ContDiff, `dPsi(wstar) = id`, fixes `wstar`).
  set Psi := deepestGConjFlat H r hr hL K wstar with hPsi
  have hcontdiff : ContDiff ℝ (⊤ : ℕ∞) Psi := contDiff_deepestGConjFlat H r hr hL K hKcd wstar
  have hderiv : HasStrictFDerivAt Psi (ContinuousLinearMap.id ℝ (Fin (flatDim H) → ℝ)) wstar :=
    hasStrictFDerivAt_deepestGConjFlat H r hr hL K hKcd hK0 wstar hbase
  have hfix : Psi wstar = wstar := deepestGConjFlat_fixpoint H r hr hL K wstar hbase
  -- `split (Psi x) = coreAbsorb⁻¹ (Ψ (coreAbsorb (split x)))` (the `split⁻¹ ∘ split` cancel).
  have hsplitPsi : ∀ x, split (Psi x)
      = (deepestCoreAbsorb H r hr hL).symm
          (deepestPsiCoreShear H r (deepestNGauge H r) K
            (deepestCoreAbsorb H r hr hL (split x))) := by
    intro x
    rw [hPsi, deepestGConjFlat]
    -- `split` and `deepestSplit … wstar` agree (`hsplit_apply`); the `.symm`/apply round-trip cancels.
    have h2 : ∀ y, split ((deepestSplit H r hr hL wstar).symm y) = y := by
      intro y
      rw [hsplit_apply, (deepestSplit H r hr hL wstar).apply_symm_apply]
    rw [h2, hsplit_apply x]
  -- The composition identity `Φcore ∘ Psi =ᶠ[𝓝 wstar] Φscore`, from the two germs.
  have hcomp : (fun x => Φcore (Psi x)) =ᶠ[nhds wstar] Φscore := by
    filter_upwards [huntwist, hreginv] with x hu hg
    rw [hΦscore, hΦcore]
    simp only [hsplitPsi x]
    -- core term: `coreAbsorb (coreAbsorb⁻¹ (…)) = …`, then `huntwist`.
    rw [(deepestCoreAbsorb H r hr hL).apply_symm_apply, hu, hg]
  -- Close via the banked diffeo bridge.
  exact rlctAtOn_diffeo_bridge_of Φscore Φcore wstar Psi
    (ContinuousLinearEquiv.refl ℝ (Fin (flatDim H) → ℝ)) hcontdiff hderiv hfix hcomp

end DLNFibre.DLN.RLCT
