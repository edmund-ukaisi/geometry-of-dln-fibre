import DLNFibre.DLN.RLCT.Validate.RouteMSchurDirectMorseP
import DLNFibre.DLN.RLCT.Validate.RouteMSchurThresholdP
import DLNFibre.DLN.RLCT.Validate.RouteMSchurCapACarveP

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurRecStepP` — the ∀p per-corank dispatch `SchurRecStep p (schurLambdaP p)`

The output-width-`p` analog of `RouteMSchurFiring.schurRecStep_four`. Dispatches on the binding stratum
via `le_or_lt (schurLambdaP p r) (p/2)`:

* **cap-B (the binding stratum is `t = 0`):** `schurLambdaP p r ≤ p/2`, so for `r ≥ 3` BOTH directMorse
  caps hold (`c' < lam r ≤ p/2` and `c' < lam r ≤ r²/2` via the threshold's `radial_le`), and
  `schurCoreP_directMorse` fires with NO recursion. This is the genuinely-hard, just-banked content.
* **cap-A (the binding stratum is interior, `t > 0`):** `schurLambdaP p r > p/2`, the recursion-driven
  carve-peel (the `Fin p` generalisation of the firing's `schurCoreGen_firing` ratio-residual carve).
  STILL OPEN — the `4 → p` transcription of the firing's `schurRatioResidGen_mid` carve chain (the
  `M22 ↦ Sc` translation-domination + the lower IH). The corank leaves `r ∈ {1, 2}` likewise route here.

`schurRecStep_p` is the SOLE remaining input to `core_schurGen_lt_top (p) (schurLambdaP p) …`, which is the
∀p R1-UPPER finiteness `routeMBoxThresholdFinite_rrp` below.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-! ## The cap-A carve-peel branch (OPEN — the `4 → p` carve transcription) -/

/-- **The cap-A / corank-leaf per-corank step (the recursion-driven branch).** For `c' < schurLambdaP p r`
NOT covered by the `t = 0` cap-B directMorse — i.e. either the binding stratum is interior
(`schurLambdaP p r > p/2`, the carve-peel) or `r ∈ {1, 2}` (the Morse / base leaves). The conclusion is
`SchurCore p r c' T`. The `Fin p` generalisation of the firing's `schurCoreGen_firing` ratio-residual
carve (`schurRatioResidGen_mid` + the lower IH `hIH` via the `M22 ↦ Sc` translation-domination) and the
`p`-general `r ∈ {1,2}` leaves.

OPEN: the `4 → p` transcription of `RouteMSchurFiring`'s carve chain (`schurRatioResidGen_mid`,
`schurResidG_translate_lt_top`, `innerSGen_eq_norm`, `zEG`, ~1170 LoC), plus the `(r,p)` `r=1,2` leaves.
Documented `sorry` on the WIP branch; the cap-B content it sits beside is real and axiom-clean. -/
theorem schurCoreP_capA (p r : ℕ) (hIH : SchurLowerIH p (schurLambdaP p) r)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < schurLambdaP p r) (T : ℝ) (hT : 0 < T) :
    SchurCore p r c' T :=
  schurCoreP_capA' p r hIH c' hc0 hc' T hT

/-! ## The ∀p per-corank dispatch -/

/-- **The ∀p per-corank firing.** `SchurRecStep p (schurLambdaP p)` — the SOLE remaining R1-UPPER input
to the ∀p finiteness. Dispatches on the binding stratum `le_or_lt (schurLambdaP p r) (p/2)`: cap-B
(`≤ p/2`, `r ≥ 3`) is `schurCoreP_directMorse` (real, no recursion); the interior / leaf cases route to
`schurCoreP_capA` (the open carve). -/
theorem schurRecStep_p (p : ℕ) : SchurRecStep p (schurLambdaP p) := by
  intro r hlam hIH c' hc0 hclt T hT
  -- the `t = 0` cap-B regime is `schurLambdaP p r ≤ p/2` AND `r ≥ 3` (directMorse's corank floor)
  rcases le_or_gt (schurLambdaP p r) ((p : ℝ) / 2) with hcap | hcap
  · -- cap-B candidate: `c' < lam r ≤ p/2`. directMorse needs `r ≥ 3`; below it falls to the leaf carve.
    rcases Nat.lt_or_ge r 3 with hr | hr
    · -- r ∈ {0,1,2}: r=0 vacuous (lam 0 = 0, c' < 0 impossible); r ∈ {1,2} the leaf carve.
      exact schurCoreP_capA p r hIH c' hc0 hclt T hT
    · -- r ≥ 3, lam r ≤ p/2: BOTH directMorse caps hold.
      have hcp : c' < (p : ℝ) / 2 := lt_of_lt_of_le hclt hcap
      have hcr : c' < (r ^ 2 : ℝ) / 2 :=
        lt_of_lt_of_le hclt (hlam.radial_le (by omega))
      exact schurCoreP_directMorse p r hr c' hc0 hcp hcr T hT
  · -- cap-A: the binding stratum is interior (`lam r > p/2`); the recursion-driven carve.
    exact schurCoreP_capA p r hIH c' hc0 hclt T hT

end DLNFibre.DLN.RLCT
