import DLNFibre.DLN.RLCT.Validate.DeepestPsiApply
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestPsiContDiff` — the absorbing diffeo `Ψ` is `ContDiff ℝ ⊤`

(#120 `hstep2`, piece 2.)

The general-`L` absorbing shear `Ψ = deepestPsiCoreShear K` is globally `ContDiff ℝ ⊤` whenever the
coupling family `K` is (`hKcd : ∀ s, ContDiff ℝ ⊤ (K s ·)`). This is the global-smoothness datum the
RLCT-invariance bridge `rlctAtOn_comp_localDiffeo` demands (it needs a global `ContDiff`, not a germ).

`Ψ` is the identity on the regular (`.1`) and spectator (`.2.2`) coordinates (both `ContDiff` as
projections), and on the core (`.2.1`) it decodes to the reduced tuple, shears each layer `S_s` by
the left factor `(1 − K_s q)`, and re-encodes. Per layer the shear `(1 − K_s q) · S_s` is
`matMulCLM (1 − K_s q) S_s` — a bounded-bilinear application (`ContDiff.clm_apply`) of the `ContDiff`
left factor `1 − K_s` and the decoded layer; `contDiff_pi'` assembles over layers and the CLE
flattening (`paramsEquivFlatCLE`) re-encodes.

The concrete DLN coupling assembly (piece 4) plugs in is a *cutoff* `Kcoup` (globally `ContDiff`, a
`= 1`-bump × the matrix-inverse coupling smooth where the pivots are invertible) — matching the
`schurCutoffShift` cutoff pattern — so its `ContDiff` hypothesis is dischargeable there.
Pure Mathlib analysis; cites nothing.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped Matrix.Norms.Elementwise

variable {L : ℕ}

/-- **The general-`L` absorbing shear `Ψ` is `ContDiff ℝ ⊤`**, for any coupling `K` that is
`ContDiff ℝ ⊤` in the split point (`hKcd`). The reg/spec coordinates are projections; the core
coordinate is the CLE flattening of the per-layer left shears `(1 − K_s q) · S_s`, each a
bounded-bilinear application of the `ContDiff` factors. -/
theorem contDiff_deepestPsiCoreShear (H : Fin (L + 1) → ℕ) (r nGauge : ℕ)
    (K : DeepestCoupling H r nGauge)
    (hKcd : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (fun q => K s q)) :
    ContDiff ℝ (⊤ : ℕ∞) (deepestPsiCoreShear H r nGauge K) := by
  -- Rewrite `Ψ` into fully-CLE form (`deepestPsiCoreShear` is phrased with the `MeasurableEquiv`
  -- `paramsEquivFlat`; the forward coerces to the CLE by `paramsEquivFlatCLE_coe`, its inverse by
  -- `hsymm` — the same rewrite the strict-deriv piece uses).
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
  -- Per-layer core shear `(1 − K_s q) · S_s` is `ContDiff` (bounded-bilinear application).
  have hlayer : ∀ s : Fin L, ContDiff ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r nGauge =>
        (1 - K s q) * ((paramsEquivFlatCLE (deepestM H r)).symm q.2.1) s) := by
    intro s
    have hrw : (fun q : DeepestSplit H r nGauge =>
          (1 - K s q) * ((paramsEquivFlatCLE (deepestM H r)).symm q.2.1) s)
        = fun q => matMulCLM (deepestM H r s.castSucc) (deepestM H r s.castSucc)
              (deepestM H r s.succ)
            (1 - K s q) (((paramsEquivFlatCLE (deepestM H r)).symm q.2.1) s) := by
      funext q; rw [matMulCLM_apply]
    rw [hrw]
    -- `q ↦ matMulCLM (1 − K_s q)` : the CLM `matMulCLM` applied to the `ContDiff` factor `1 − K_s`.
    have hleft : ContDiff ℝ (⊤ : ℕ∞) (fun q : DeepestSplit H r nGauge =>
        (matMulCLM (deepestM H r s.castSucc) (deepestM H r s.castSucc) (deepestM H r s.succ))
          (1 - K s q)) :=
      (matMulCLM (deepestM H r s.castSucc) (deepestM H r s.castSucc)
        (deepestM H r s.succ)).contDiff.comp
        ((contDiff_const (c := (1 : Matrix (Fin (deepestM H r s.castSucc))
          (Fin (deepestM H r s.castSucc)) ℝ))).sub (hKcd s))
    -- `q ↦ (decode q.2.1) s` : project layer `s` of the CLE-decoded core coordinate.
    have hright : ContDiff ℝ (⊤ : ℕ∞) (fun q : DeepestSplit H r nGauge =>
        ((paramsEquivFlatCLE (deepestM H r)).symm q.2.1) s) :=
      (ContinuousLinearMap.proj s).contDiff.comp
        ((paramsEquivFlatCLE (deepestM H r)).symm.contDiff.comp (contDiff_fst.comp contDiff_snd))
    exact hleft.clm_apply hright
  -- Assemble the core (pi over layers, then the CLE re-encode) with the reg/spec projections.
  have hcore : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r nGauge =>
        paramsEquivFlatCLE (deepestM H r)
          (fun s => (1 - K s q) * ((paramsEquivFlatCLE (deepestM H r)).symm q.2.1) s)) :=
    (paramsEquivFlatCLE (deepestM H r)).contDiff.comp (contDiff_pi' hlayer)
  exact contDiff_fst.prodMk (hcore.prodMk (contDiff_snd.comp contDiff_snd))

/-- **The absorbing shear `Ψ` is a local diffeomorphism at the split basepoint** — the exact triple
`rlctAtOn_comp_localDiffeo` consumes: globally `ContDiff ℝ ⊤` (piece 2), strict Fréchet derivative
the identity at `0` (piece 3-apply, `dΨ(0) = I`), and fixing `0` (`deepestPsiCoreShear_basepoint`).
Given a coupling `K` globally `ContDiff` (`hKcd`) and vanishing at the basepoint (`hK0`). The strict
differentiability of `K` at `0` that piece-3-apply needs is derived internally from `hKcd`
(`ContDiffAt.hasStrictFDerivAt`), so the interface carries only the two essential hypotheses — the
derivative VALUE is absorbed by piece-3-apply's vanishing right factor. Packages the analytic input to
the RLCT-invariance bridge; the assembly (#120 `hstep2`, piece 5) supplies the concrete cutoff `Kcoup`
for `hKcd`/`hK0` plus the untwisting `Score = coreΦ ∘ coreAbsorb ∘ Ψ`. -/
theorem deepestPsiCoreShear_isLocalDiffeoAt (H : Fin (L + 1) → ℕ) (r nGauge : ℕ)
    (K : DeepestCoupling H r nGauge)
    (hKcd : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (fun q => K s q))
    (hK0 : ∀ s, K s 0 = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (deepestPsiCoreShear H r nGauge K) ∧
      HasStrictFDerivAt (deepestPsiCoreShear H r nGauge K)
        (ContinuousLinearMap.id ℝ (DeepestSplit H r nGauge)) 0 ∧
      deepestPsiCoreShear H r nGauge K 0 = 0 :=
  ⟨contDiff_deepestPsiCoreShear H r nGauge K hKcd,
    hasStrictFDerivAt_deepestPsiCoreShear H r nGauge K hK0
      (fun s => ⟨fderiv ℝ (fun q => K s q) 0, ((hKcd s).contDiffAt).hasStrictFDerivAt (by simp)⟩),
    deepestPsiCoreShear_basepoint H r nGauge K⟩

end DLNFibre.DLN.RLCT
