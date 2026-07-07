import DLNFibre.DLN.RLCT.Validate.DeepestSplitSmooth
import DLNFibre.DLN.RLCT.Validate.DeepestSchurSmooth
import DLNFibre.DLN.RLCT.Validate.DeepestSplitConcrete

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestPsiFlatCutGen` — the general cutoff→flat-diffeo plumbing (#120 `hstep2`, item 1 analytic half)

The **chain-independent analytic plumbing** of the general-`L` Step Ψ_conj: given ANY raw split-side
move `psiSplitRaw : DeepestSplit → DeepestSplit` that fixes the split origin, is `ContDiffAt` on a bump
support, and whose deviation `psiSplitRaw − id` has vanishing strict derivative at `0`, this module
builds the concrete flat diffeo `psi = split⁻¹ ∘ (cutoff psiSplitRaw) ∘ split` and discharges the four
hypotheses `deepest_diffeo_bridge_gen_assembled` (`DeepestDiffeoBridgeGenConj`) consumes for its
abstract `psi`:

* `contDiff_deepestPsiFlatCut` — `ContDiff ℝ ⊤ psi` (`split^±` affine + the χ-smoothed cutoff);
* `hasStrictFDerivAt_deepestPsiFlatCut` — `D(psi)(wstar) = id` (the chain `splitCLE⁻¹ ∘ id ∘ splitCLE`,
  the cutoff's `D(0) = id` from `D(psiSplitRaw − id)(0) = 0` + the origin fixpoint);
* `deepestPsiFlatCut_fixpoint` — `psi wstar = wstar` (`split wstar = 0`, cutoff fixes `0`);
* `deepestPsiFlatCut_split_germ` — `∀ᶠ x near wstar, split (psi x) = psiSplitRaw (split x)` (the χ = 1
  germ: near the basepoint the cutoff IS the raw move).

Abstracting over `psiSplitRaw` (Codex-vetted as faithful: the geometric joint-move DEFINITION and the
two germs `hsub3reg`/`hsub4core` remain to be supplied — they are the coupled bulk). Mirrors the L=2
`psiSplitCutL2Conj`/`psiL2Conj` cutoff apparatus (`DeepestDiffeoBridgeL2Conj`), abstracting away the
concrete `psiSplitRawL2CoreConj`.
-/

open MeasureTheory Topology
open scoped ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The χ-cutoff of a raw split-side move**: `q + χ(q)·(psiSplitRaw q − q)`. Equals the identity where
`χ = 0` (off the support) and the raw move where `χ = 1` (near the origin). -/
noncomputable def deepestPsiCutRaw (H : Fin (L + 1) → ℕ) (r : ℕ)
    (psiSplitRaw : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)))
    (q : DeepestSplit H r (deepestNGauge H r)) : DeepestSplit H r (deepestNGauge H r) :=
  q + (χ q : ℝ) • (psiSplitRaw q - q)

/-- **The general cutoff FLAT joint move** `split⁻¹ ∘ (cutoff psiSplitRaw) ∘ split`, for the concrete
`split = deepestSplit … wstar`. The `psi` the assembled bridge consumes. -/
noncomputable def deepestPsiFlatCut (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (psiSplitRaw : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)))
    (wstar : Fin (flatDim H) → ℝ) : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ) :=
  fun w => (deepestSplit H r hr hL wstar).symm
    (deepestPsiCutRaw H r psiSplitRaw χ (deepestSplit H r hr hL wstar w))

/-- **The cutoff move fixes the split origin** (`cutoff psiSplitRaw 0 = 0`), given `psiSplitRaw 0 = 0`:
`0 + χ(0)·(0 − 0) = 0`. -/
theorem deepestPsiCutRaw_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (psiSplitRaw : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)))
    (hraw0 : psiSplitRaw 0 = 0) :
    deepestPsiCutRaw H r psiSplitRaw χ (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
  simp only [deepestPsiCutRaw, hraw0, sub_self, smul_zero, add_zero]

/-- **`ContDiff ℝ ⊤` of the cutoff move** (`id + χ·δ`, with `δ = psiSplitRaw − id` `ContDiffAt` on
`tsupport χ`). -/
theorem contDiff_deepestPsiCutRaw (H : Fin (L + 1) → ℕ) (r : ℕ)
    (psiSplitRaw : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)))
    (hcd : ∀ q ∈ tsupport (fun y => ((χ y : ℝ))),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun q => psiSplitRaw q - q) q) :
    ContDiff ℝ (⊤ : ℕ∞) (deepestPsiCutRaw H r psiSplitRaw χ) := by
  have hcorr : ContDiff ℝ (⊤ : ℕ∞) (fun q => (χ q : ℝ) • (psiSplitRaw q - q)) :=
    contDiff_contDiffBump_smul χ (fun q => psiSplitRaw q - q) hcd
  have heq : deepestPsiCutRaw H r psiSplitRaw χ
      = fun q => q + (χ q : ℝ) • (psiSplitRaw q - q) := rfl
  rw [heq]; exact contDiff_id.add hcorr

/-- **The cutoff move has strict derivative `id` at the split origin** (`D(δ)(0) = 0`, `δ(0) = 0`,
scalar–vector product rule). Mirrors `hasStrictFDerivAt_psiSplitCutL2Conj_zero`. -/
theorem hasStrictFDerivAt_deepestPsiCutRaw_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (psiSplitRaw : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)))
    (hraw0 : psiSplitRaw 0 = 0)
    (hderiv0 : HasStrictFDerivAt (fun q => psiSplitRaw q - q)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r)) 0) :
    HasStrictFDerivAt (deepestPsiCutRaw H r psiSplitRaw χ)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r)))
      (0 : DeepestSplit H r (deepestNGauge H r)) := by
  have hχ : HasStrictFDerivAt (fun q => (χ q : ℝ))
      (fderiv ℝ (fun q => (χ q : ℝ)) 0) (0 : DeepestSplit H r (deepestNGauge H r)) :=
    (χ.contDiff (n := (1 : ℕ∞))).hasStrictFDerivAt (by norm_num)
  have hsmul := hχ.smul hderiv0
  simp only [hraw0, sub_zero, smul_zero, ContinuousLinearMap.smulRight_zero, add_zero] at hsmul
  have hid : HasStrictFDerivAt (fun q : DeepestSplit H r (deepestNGauge H r) => q)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r))) 0 :=
    hasStrictFDerivAt_id 0
  have hsum := hid.add hsmul
  rw [add_zero] at hsum
  exact hsum.congr_of_eventuallyEq (by filter_upwards with q; rfl)

/-- **`ContDiff ℝ ⊤` of the flat cutoff move** (`split⁻¹ ∘ cutoff ∘ split`). -/
theorem contDiff_deepestPsiFlatCut (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (psiSplitRaw : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)))
    (hcd : ∀ q ∈ tsupport (fun y => ((χ y : ℝ))),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun q => psiSplitRaw q - q) q)
    (wstar : Fin (flatDim H) → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (deepestPsiFlatCut H r hr hL psiSplitRaw χ wstar) := by
  have heq : deepestPsiFlatCut H r hr hL psiSplitRaw χ wstar
      = fun w => (deepestSplit H r hr hL wstar).symm
          (deepestPsiCutRaw H r psiSplitRaw χ (deepestSplit H r hr hL wstar w)) := rfl
  rw [heq]
  exact (contDiff_deepestSplit_symm H r hr hL wstar).comp
    ((contDiff_deepestPsiCutRaw H r psiSplitRaw χ hcd).comp
      (contDiff_deepestSplit H r hr hL wstar))

/-- **The flat cutoff move fixes `wstar`** (`split wstar = 0`, cutoff fixes `0`, `split⁻¹ 0 = wstar`). -/
theorem deepestPsiFlatCut_fixpoint (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (psiSplitRaw : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)))
    (hraw0 : psiSplitRaw 0 = 0)
    (wstar : Fin (flatDim H) → ℝ)
    (hbase : deepestSplit H r hr hL wstar wstar = 0) :
    deepestPsiFlatCut H r hr hL psiSplitRaw χ wstar wstar = wstar := by
  simp only [deepestPsiFlatCut, hbase, deepestPsiCutRaw_zero H r psiSplitRaw χ hraw0]
  rw [← hbase, (deepestSplit H r hr hL wstar).symm_apply_apply]

/-- **The flat cutoff move has strict derivative `id` at `wstar`** (chain rule: `split` CLE at `wstar`,
`id` at the origin via `hasStrictFDerivAt_deepestPsiCutRaw_zero`, `split⁻¹` CLE; `e = refl`). Mirrors
`psiL2Conj_hasStrictFDerivAt`. -/
theorem hasStrictFDerivAt_deepestPsiFlatCut (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (psiSplitRaw : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)))
    (hraw0 : psiSplitRaw 0 = 0)
    (hderiv0 : HasStrictFDerivAt (fun q => psiSplitRaw q - q)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r)) 0)
    (wstar : Fin (flatDim H) → ℝ)
    (hbase : deepestSplit H r hr hL wstar wstar = 0) :
    HasStrictFDerivAt (deepestPsiFlatCut H r hr hL psiSplitRaw χ wstar)
      (ContinuousLinearMap.id ℝ (Fin (flatDim H) → ℝ)) wstar := by
  have hsplit := hasStrictFDerivAt_deepestSplit H r hr hL wstar wstar
  have hcut0 := hasStrictFDerivAt_deepestPsiCutRaw_zero H r psiSplitRaw χ hraw0 hderiv0
  have hcut : HasStrictFDerivAt (deepestPsiCutRaw H r psiSplitRaw χ)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r)))
      (deepestSplit H r hr hL wstar wstar) := by rw [hbase]; exact hcut0
  have hsymm := hasStrictFDerivAt_deepestSplit_symm H r hr hL wstar
    (deepestPsiCutRaw H r psiSplitRaw χ (deepestSplit H r hr hL wstar wstar))
  have hcomp := hsymm.comp wstar (hcut.comp wstar hsplit)
  refine hcomp.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  exact (deepestSplitCLE H r hr hL).symm_apply_apply w

/-- **The split-compatibility germ** `∀ᶠ x near wstar, split (psi x) = psiSplitRaw (split x)`. Near the
basepoint `χ = 1` (bump), so the cutoff IS the raw move; `split ∘ split⁻¹` cancels. Mirrors
`psiL2Conj_eventuallyEq_psiRawL2Conj` composed with the split conjugacy. -/
theorem deepestPsiFlatCut_split_germ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (psiSplitRaw : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)))
    (wstar : Fin (flatDim H) → ℝ)
    (hbase : deepestSplit H r hr hL wstar wstar = 0) :
    ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds wstar,
      deepestSplit H r hr hL wstar (deepestPsiFlatCut H r hr hL psiSplitRaw χ wstar x)
        = psiSplitRaw (deepestSplit H r hr hL wstar x) := by
  -- `χ = 1` near `wstar` (split → 0, χ = 1 near 0).
  have htend : Filter.Tendsto (deepestSplit H r hr hL wstar) (nhds wstar) (nhds 0) := by
    rw [← hbase]; exact (deepestSplit H r hr hL wstar).continuous.continuousAt
  have hχ1 : (fun x => ((χ (deepestSplit H r hr hL wstar x) : ℝ))) =ᶠ[nhds wstar] 1 :=
    htend.eventually χ.eventuallyEq_one
  filter_upwards [hχ1] with x hx
  have hx' : ((χ (deepestSplit H r hr hL wstar x) : ℝ)) = 1 := hx
  rw [deepestPsiFlatCut, (deepestSplit H r hr hL wstar).apply_symm_apply, deepestPsiCutRaw, hx',
    one_smul, add_sub_cancel]

end DLNFibre.DLN.RLCT
