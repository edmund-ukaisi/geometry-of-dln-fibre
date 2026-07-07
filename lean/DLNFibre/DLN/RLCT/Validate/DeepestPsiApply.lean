import DLNFibre.DLN.RLCT.Validate.DeepestPsi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestPsiApply` — the absorbing diffeo has `dΨ(0) = I`

(#120 `hstep2`, piece 3-apply.)

Assembles the banked pieces into the strict-derivative fact the RLCT-invariance bridge needs:
the general-`L` absorbing shear `Ψ = deepestPsiCoreShear K` has strict Fréchet derivative the
**identity** at the split basepoint `0`, provided the coupling `K` vanishes there (`K_s 0 = 0`) and
is strictly differentiable there.

The assembly (all pieces are DLN-free / cite nothing):
- **reg / spec coordinates** — `Ψ` is the identity, so those components differentiate to the
  product projections `fst` and `snd ∘ snd`;
- **core coordinate** — `Ψ` decodes the core `q.2.1` to a reduced tuple, shears each layer by the
  left factor `(1 − K_s q)`, and re-encodes. Per layer,
  `hasStrictFDerivAt_bilinear_of_right_zero` (piece 3-core) with `B = matMulCLM` (piece 3) applies:
  the right factor (the decoded layer) vanishes at `0`, so the derivative is the decode-projection;
  at `0` the left factor is `1 − K_s 0 = 1` and `matMulCLM 1 = id`, so the core-block derivative is
  the encode ∘ decode = identity round-trip, i.e. the core projection `q ↦ q.2.1`;
- combining the three by `HasStrictFDerivAt.prodMk` gives derivative
  `q ↦ (q.1, (q.2.1, q.2.2)) = q`, the identity.

Everything is stated against the CLE packaging `paramsEquivFlatCLE` of the flattening (needed for
the strict Fréchet derivative — the `MeasurableEquiv` packaging does not carry one); the coe
agreement `paramsEquivFlatCLE_coe` (and its inline `symm` companion) bridges back to the
`deepestPsiCoreShear` definition, which is phrased with the `MeasurableEquiv` `paramsEquivFlat`.
-/

namespace DLNFibre.DLN.RLCT

open scoped Topology
open Matrix
open scoped Matrix.Norms.Elementwise

variable {L : ℕ}

/-- **The general-`L` absorbing shear `Ψ` has strict derivative the identity at the basepoint**
(`dΨ(0) = I`), for any coupling `K` that vanishes at the basepoint (`K_s 0 = 0`) and is strictly
differentiable there. This is the fixed-point-with-identity-derivative datum
`rlctAtOn_comp_localDiffeo` needs to transport the RLCT across `Ψ`.

The reg/spec coordinates are untouched (derivatives `fst`, `snd ∘ snd`); the core coordinate shears
by `(1 − K_s q)` on the decoded layer, whose right factor vanishes at `0`, so
`hasStrictFDerivAt_bilinear_of_right_zero` with `matMulCLM` gives the decode-projection, and the
left factor `1 − K_s 0 = 1` (with `matMulCLM 1 = id`) leaves it the encode∘decode round-trip. -/
theorem hasStrictFDerivAt_deepestPsiCoreShear (H : Fin (L + 1) → ℕ) (r nGauge : ℕ)
    (K : DeepestCoupling H r nGauge) (hK0 : ∀ s, K s 0 = 0)
    (hKderiv : ∀ s, ∃ K' : DeepestSplit H r nGauge →L[ℝ]
        Matrix (Fin (deepestM H r s.castSucc)) (Fin (deepestM H r s.castSucc)) ℝ,
        HasStrictFDerivAt (fun q => K s q) K' 0) :
    HasStrictFDerivAt (deepestPsiCoreShear H r nGauge K)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r nGauge)) 0 := by
  -- Rewrite `Ψ` into a fully-CLE form (the strict derivative needs the CLE, not `MeasurableEquiv`)
  -- `(paramsEquivFlatCLE M).symm` and `(paramsEquivFlat M).symm` coerce to the same function
  -- (both invert the shared forward map `paramsEquivFlatCLE_coe`); the `symm` companion.
  have hsymm : ⇑(paramsEquivFlatCLE (deepestM H r)).symm
      = ⇑(paramsEquivFlat (deepestM H r)).symm := by
    funext y
    apply (paramsEquivFlat (deepestM H r)).injective
    rw [(paramsEquivFlat (deepestM H r)).apply_symm_apply, ← paramsEquivFlatCLE_coe,
      (paramsEquivFlatCLE (deepestM H r)).apply_symm_apply]
  have hΨ : deepestPsiCoreShear H r nGauge K
      = fun q : DeepestSplit H r nGauge =>
        (q.1, (paramsEquivFlatCLE (deepestM H r)
          (fun s => (1 - K s q) * ((paramsEquivFlatCLE (deepestM H r)).symm q.2.1) s),
            q.2.2)) := by
    funext q
    unfold deepestPsiCoreShear
    simp only [paramsEquivFlatCLE_coe, hsymm]
  rw [hΨ]
  -- Component derivatives: reg (`fst`), spec (`snd ∘ snd`), and the core-projection helper.
  have hreg : HasStrictFDerivAt (fun q : DeepestSplit H r nGauge => q.1)
      (ContinuousLinearMap.fst ℝ _ _) 0 := hasStrictFDerivAt_fst
  have hspec : HasStrictFDerivAt (fun q : DeepestSplit H r nGauge => q.2.2)
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)) 0 :=
    hasStrictFDerivAt_snd.comp 0 hasStrictFDerivAt_snd
  have hπ : HasStrictFDerivAt (fun q : DeepestSplit H r nGauge => q.2.1)
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)) 0 :=
    hasStrictFDerivAt_fst.comp 0 hasStrictFDerivAt_snd
  -- The core shear differentiates to the decode-projection (per layer, via the bilinear scaffold).
  have hshearN : HasStrictFDerivAt
      (fun q : DeepestSplit H r nGauge =>
        (fun s => (1 - K s q) * ((paramsEquivFlatCLE (deepestM H r)).symm q.2.1) s :
          Params (deepestM H r)))
      (((paramsEquivFlatCLE (deepestM H r)).symm :
          (Fin (flatDim (deepestM H r)) → ℝ) →L[ℝ] Params (deepestM H r)).comp
        ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))) 0 := by
    refine hasStrictFDerivAt_pi''
      (F' := fun s : Fin L => Fin (deepestM H r s.castSucc) → Fin (deepestM H r s.succ) → ℝ) ?_
    intro s
    -- left factor `g = 1 − K_s`, strictly differentiable (value irrelevant, absorbed at `0`).
    have hg := (hasStrictFDerivAt_const (𝕜 := ℝ)
        (1 : Matrix (Fin (deepestM H r s.castSucc)) (Fin (deepestM H r s.castSucc)) ℝ)
        (0 : DeepestSplit H r nGauge)).sub (hKderiv s).choose_spec
    -- right factor `f = decode-then-project-then-eval-at-s`, a composition of CLMs.
    have hf : HasStrictFDerivAt
        (fun q : DeepestSplit H r nGauge => ((paramsEquivFlatCLE (deepestM H r)).symm q.2.1) s)
        ((ContinuousLinearMap.proj s).comp
          (((paramsEquivFlatCLE (deepestM H r)).symm :
              (Fin (flatDim (deepestM H r)) → ℝ) →L[ℝ] Params (deepestM H r)).comp
            ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))) 0 :=
      (ContinuousLinearMap.proj s).hasStrictFDerivAt.comp 0
        (((paramsEquivFlatCLE (deepestM H r)).symm.hasStrictFDerivAt).comp 0 hπ)
    -- the right factor vanishes at the basepoint.
    have hf0 : ((paramsEquivFlatCLE (deepestM H r)).symm ((0 : DeepestSplit H r nGauge).2.1)) s
        = 0 := by
      simp only [Prod.snd_zero, Prod.fst_zero, map_zero]; rfl
    have hmech := hasStrictFDerivAt_bilinear_of_right_zero
      (matMulCLM (deepestM H r s.castSucc) (deepestM H r s.castSucc) (deepestM H r s.succ))
      hg hf hf0
    simp only [matMulCLM_apply, Pi.sub_apply, hK0, sub_zero, matMulCLM_one,
      ContinuousLinearMap.id_comp] at hmech
    exact hmech
  -- Compose the CLE flattening onto the core shear.
  have hcore := (paramsEquivFlatCLE (deepestM H r)).hasStrictFDerivAt.comp
    (0 : DeepestSplit H r nGauge) hshearN
  -- Assemble the three components and identify the total derivative with the identity.
  have hderiv_eq :
      (ContinuousLinearMap.fst ℝ _ _).prod
        ((((paramsEquivFlatCLE (deepestM H r)) :
            Params (deepestM H r) →L[ℝ] (Fin (flatDim (deepestM H r)) → ℝ)).comp
          (((paramsEquivFlatCLE (deepestM H r)).symm :
              (Fin (flatDim (deepestM H r)) → ℝ) →L[ℝ] Params (deepestM H r)).comp
            ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))).prod
          ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))
        = ContinuousLinearMap.id ℝ (DeepestSplit H r nGauge) := by
    refine ContinuousLinearMap.ext (fun q => ?_)
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearMap.id_apply, Prod.mk.eta]
  rw [← hderiv_eq]
  exact hreg.prodMk (hcore.prodMk hspec)

end DLNFibre.DLN.RLCT
