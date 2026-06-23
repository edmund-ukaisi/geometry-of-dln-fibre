import DLNFibre.DLN.RLCT.Validate.DeepestRegAbsorbIFT
import DLNFibre.DLN.RLCT.Validate.DeepestFramedProduct
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFramedDeriv` — strict-derivative of `deepestEPivot` at `0`

The standalone analytic lemma feeding `deepestEPivot_deriv` (`DeepestGaugeConstruction.lean`, PIN 1
of the L2 gauge-chart assembly). The consumer needs the bundle

    ∃ (D_E : (R × S) →L[ℝ] R) (e : DeepestSplit ≃L[ℝ] DeepestSplit),
      HasStrictFDerivAt deepestEPivot D_E 0  ∧  (e : →L) = regStraightenTotalCLM D_E

with `e` a genuine `ContinuousLinearEquiv` (the downstream `rlctAtOn_comp_localDiffeo` builds a
local diffeo from `HasStrictFDerivAt f (e:→L) wstar`, so `regStraightenTotalCLM D_E` is invertible).

## The two pieces, and the one fenced fact

1. **The strict derivative is FREE.** `deepestEPivot` is `ContDiff ⊤` (`deepestEPivot_contdiff`), so
   `ContDiff.hasStrictFDerivAt` gives `HasStrictFDerivAt deepestEPivot (fderiv ℝ deepestEPivot 0) 0`
   for the supplied `D_E = fderiv ℝ deepestEPivot 0`. No from-scratch product-derivative grind is
   needed for the strict-derivative existence — the proven `ContDiff` carries it.

2. **The invertible `e` needs the SHEAR FORM of `D_E`.** `regStraightenTotalCLM D_E (δ) =
   (D_E (δ.1, δ.2.2), δ.2.1, δ.2.2)` is block-lower-triangular; it is a `ContinuousLinearEquiv` iff
   its reg→reg part `D_E (·, 0) : R →L R` is a linear iso. The g213/g239 cert: the sandwich
   derivative `dP|_0 = Σ_s blockdiag[I,0]·δC_s·blockdiag[I,0]` keeps `(Σ_s δX_s, δY_L, δZ_1)`, and
   on the boundary-pivot coordinates the reg→reg part is the IDENTITY (`det = 1`), so `D_E` has the
   form `fst_R + (gauge-coupling) ∘ snd_S`. With that form `regStraightenTotalCLM D_E = id + N` with
   `N` SQUARE-ZERO (`N` reads gauge → reg; reapplying reads the reg-output's gauge slot `= 0`), so
   `e := clmShearEquiv N` is a genuine `≃L` (inverse `id − N`).

   **The fenced fact** (`IsRegShearDeriv` below): that `fderiv ℝ deepestEPivot 0` has the shear form
   `fst + G ∘ snd`. This is the index-alignment between the OPAQUE pack `regResidualPack` (used by
   `deepestEPivot`) and the OPAQUE slot-read `regGaugeSlotEquiv` (used by `framedParamsReg`) — both
   `Fintype.equivFin`-based. It is a DEFINITION-LEVEL property of those equivalences (whether the
   reg slot maps onto the boundary generators identically), NOT provable from a leaf without pinning
   the pack convention (the g239 "`_deriv` obstruction" / the #120 boundary-generator equiv that
   replaces the opaque pack). Carried as a named hypothesis so the bundle is sorry-free and the
   obstruction lives next to the claim.

## Closable here, standalone and sorry-free

- `regShearN` + the square-zero algebra for `regStraightenTotalCLM (fst + G ∘ snd)` (reusing
  `clmShearEquiv` from `DeepestRegAbsorbIFT`).
- `deepestEPivot_hasStrictFDerivAt`: the strict derivative free from `ContDiff`.
- `deepestEPivot_deriv_of_shear`: given the shear form, the consumer bundle (`e` the square-zero
  shear `≃L`). cobuild applies it once the single-writer supplies the shear-form fact.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The square-zero shear from a `fst + G ∘ snd` reg-derivative

Abstract over the slot types `R` (reg), `C` (core), `S` (gauge/spectator). For a reg-derivative
`D_E : (R × S) →L R` of the shear form `fst_R + G ∘ snd_S` (reg→reg part the identity, gauge→reg the
coupling `G`), `regStraightenTotalCLM D_E` on `R × (C × S)` is `id + N` with `N` square-zero,
hence a `ContinuousLinearEquiv`. Layout-independent — `G` (and the index pack) stay abstract. -/

section ShearEquiv
variable {R C S : Type*}
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The square-zero perturbation `N : R × (C × S) →L R × (C × S)`, `δ ↦ (G δ.2.2, 0, 0)`, from a
gauge→reg coupling `G : S →L R`. Reads the gauge slot into reg; writes `0` to core + gauge. -/
noncomputable def regShearN (G : S →L[ℝ] R) :
    (R × (C × S)) →L[ℝ] (R × (C × S)) :=
  (G.comp ((ContinuousLinearMap.snd ℝ C S).comp (ContinuousLinearMap.snd ℝ R (C × S)))).prod 0

@[simp] theorem regShearN_apply (G : S →L[ℝ] R) (δ : R × (C × S)) :
    regShearN (C := C) G δ = (G δ.2.2, 0) := rfl

/-- `regShearN G` is **square-zero**: reapplying reads the reg-output's gauge slot, which is `0`. -/
theorem regShearN_comp_self (G : S →L[ℝ] R) :
    (regShearN (C := C) G).comp (regShearN (C := C) G) = 0 := by
  ext δ <;> simp [regShearN_apply]

/-- The shear `regStraightenTotalCLM (fst + G ∘ snd) = id + regShearN G`. The reg→reg identity part
becomes the diagonal `id`; the gauge→reg coupling `G` becomes the off-diagonal `N`. -/
theorem regStraightenTotalCLM_fst_add_eq (G : S →L[ℝ] R) :
    regStraightenTotalCLM (C := C)
        (ContinuousLinearMap.fst ℝ R S + G.comp (ContinuousLinearMap.snd ℝ R S))
      = ContinuousLinearMap.id ℝ (R × (C × S)) + regShearN (C := C) G := by
  ext δ <;>
    simp [regStraightenTotalCLM, regShearN_apply, ContinuousLinearMap.add_apply]

/-- The invertible shear `e` from a gauge→reg coupling `G`: `clmShearEquiv (regShearN G)`, a genuine
`ContinuousLinearEquiv` (inverse `id − N`); coerces to `regStraightenTotalCLM (fst+G·snd)`. -/
noncomputable def regShearEquiv (G : S →L[ℝ] R) :
    (R × (C × S)) ≃L[ℝ] (R × (C × S)) :=
  clmShearEquiv (regShearN (C := C) G) (regShearN_comp_self (C := C) G)

/-- `regShearEquiv G`, coerced to a `→L`, IS `regStraightenTotalCLM (fst + G ∘ snd)`. -/
theorem regShearEquiv_coe (G : S →L[ℝ] R) :
    (regShearEquiv (C := C) G : (R × (C × S)) →L[ℝ] (R × (C × S)))
      = regStraightenTotalCLM (C := C)
          (ContinuousLinearMap.fst ℝ R S + G.comp (ContinuousLinearMap.snd ℝ R S)) := by
  rw [regShearEquiv, clmShearEquiv_coe, regStraightenTotalCLM_fst_add_eq]

end ShearEquiv

/-! ## The strict derivative of `deepestEPivot` (free from `ContDiff`)

`deepestEPivot` is `ContDiff ⊤` (`deepestEPivot_contdiff`), so its `fderiv` at `0` is also a STRICT
derivative (`ContDiff.hasStrictFDerivAt`). No from-scratch product-derivative grind is needed —
the proven smoothness carries it; the only open content is the *value* identification (the
shear form), fenced below. -/

/-- **`deepestEPivot` has a strict Fréchet derivative at `0`**, equal to its `fderiv`. Immediate
from `deepestEPivot_contdiff` (`ContDiff ⊤ ⟹ HasStrictFDerivAt _ (fderiv) _`). The bundle's `D_E` is
this `fderiv`; its concrete shear form is the fenced `IsRegShearDeriv` fact. -/
theorem deepestEPivot_hasStrictFDerivAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    HasStrictFDerivAt (deepestEPivot H r hr hL)
      (fderiv ℝ (deepestEPivot H r hr hL) 0) 0 :=
  (deepestEPivot_contdiff H r hr hL).hasStrictFDerivAt (by simp)

/-! ## The fenced shear-form fact and the consumer bundle

`IsRegShearDeriv` asserts `deepestEPivot`'s derivative at `0` has the shear form `fst + G ∘ snd` for
some gauge→reg coupling `G` — equivalently, its reg→reg part is the identity (`dE(0) = id` on the
boundary-pivot coordinates, g213). This is the index-alignment between the opaque `regResidualPack`
(in `deepestEPivot`) and the opaque `regGaugeSlotEquiv` (in `framedParamsReg`): both are
`Fintype.equivFin`-based, so the alignment is a DEFINITION-LEVEL property — not provable from a leaf
without pinning the pack (the g239 `_deriv` obstruction / #120 boundary-generator equiv). Carried
as a hypothesis so the consumer bundle is sorry-free. -/

/-- **The shear-form fact for `deepestEPivot`'s deriv at `0`** (the fenced alignment obligation).
A gauge→reg coupling `G` with `fderiv ℝ deepestEPivot 0 = fst + G ∘ snd` — the reg→reg part the
identity (`dE(0) = id` on the boundary-pivot coordinates, g213). DEFINITION-level: the alignment of
`regResidualPack` with `regGaugeSlotEquiv`'s reg slot, owned by the single-writer of those defs. -/
def IsRegShearDeriv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) : Prop :=
  ∃ G : (Fin (deepestNGauge H r) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ),
    fderiv ℝ (deepestEPivot H r hr hL) 0
      = ContinuousLinearMap.fst ℝ (Fin (deepestNReg H r) → ℝ) (Fin (deepestNGauge H r) → ℝ)
        + G.comp
            (ContinuousLinearMap.snd ℝ (Fin (deepestNReg H r) → ℝ) (Fin (deepestNGauge H r) → ℝ))

/-- **The consumer bundle, conditional on the shear-form fact** (`deepestEPivot_deriv` shape). Given
`IsRegShearDeriv` (the fenced alignment fact, `fderiv = fst + G ∘ snd`), exhibit the concrete `D_E`
(`= fderiv`, so `HasStrictFDerivAt` is free from `ContDiff`) and the invertible shear `e`
(`= regShearEquiv G`, a genuine `≃L`) with `(e : →L) = regStraightenTotalCLM D_E`. This is the exact
∃-shape `deepestEPivot_deriv` (`DeepestGaugeConstruction.lean:431`) claims; cobuild applies it once
the single-writer supplies `IsRegShearDeriv` for the pinned pack. -/
theorem deepestEPivot_deriv_of_shear (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hshear : IsRegShearDeriv H r hr hL) :
    ∃ (D_E : ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) →L[ℝ]
        (Fin (deepestNReg H r) → ℝ))
      (e : DeepestSplit H r (deepestNGauge H r) ≃L[ℝ] DeepestSplit H r (deepestNGauge H r)),
      HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 ∧
      (e : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r))
        = regStraightenTotalCLM D_E := by
  obtain ⟨G, hG⟩ := hshear
  refine ⟨fderiv ℝ (deepestEPivot H r hr hL) 0, ?_, deepestEPivot_hasStrictFDerivAt H r hr hL, ?_⟩
  · -- The invertible shear `e := regShearEquiv G` (genuine `≃L`).
    exact regShearEquiv (C := Fin (flatDim (deepestM H r)) → ℝ) G
  · -- `(e:→L) = regStraightenTotalCLM (fderiv)`: rw `fderiv` by `hG`, then `regShearEquiv_coe`.
    rw [hG, regShearEquiv_coe]

end DLNFibre.DLN.RLCT
