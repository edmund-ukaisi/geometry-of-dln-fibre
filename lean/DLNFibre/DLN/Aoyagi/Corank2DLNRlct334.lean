import DLNFibre.DLN.Aoyagi.Corank2EwrapMeasure
import DLNFibre.DLN.Aoyagi.Corank2OverVanishHeadline334

/-!
# `DLN.Aoyagi.Corank2DLNRlct334` — the UNCONDITIONAL (3,3,4) DLN square-Frobenius V-lower

Wires the core-loss V-lower headline `OverVanishHeadline334.rlctAt_coreGen334_ge_four`
(`4 ≤ rlctAt (∑(coreGen dvec eWrap)ᵢ²) 0`) to the ACTUAL DLN square-Frobenius loss RLCT
`rlctGlobal (lossDLN ![3,3,4] 0)` via `coreReduction` (`LearningCoefficient`), with the reduction's
sole un-banked input `MeasurePreserving eWrap` now DISCHARGED (`Corank2EwrapMeasure`).

Result: `(4 : ℝ) ≤ rlctGlobal (lossDLN ![3,3,4] 0)`, UNCONDITIONAL — no `MeasurePreserving eWrap`
hypothesis, cite-free, monument-free. This is the honest "the `(3,3,4)` DLN square-Frobenius RLCT is
`≥ 4`" (the geometric V-lower; the matching `≤ 4` upper is `Corank2CiteFree334`, likewise now
dischargeable via `measurePreserving_eWrap`). Because that upper is cite-free (a single-chart
change-of-variables, NOT the Watanabe bound), the `(3,3,4)` `rlct = ½·codim = 4` equality is FULLY
cite-free — assembled in `Corank2Equality334` (`dln_rlct334_eq_half_codim`). This file contributes
the geometric lower half `rlct ≥ 4`.
-/

open MeasureTheory
open DLNFibre.Core DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi

open DLNFibre.DLN (lossDLN)

/-- **The UNCONDITIONAL (3,3,4) DLN square-Frobenius V-lower**: `4 ≤ rlctGlobal (lossDLN ![3,3,4] 0)`.
The deepest-point + measure-preserving-flatten reduction `coreReduction` (fed the now-proven
`measurePreserving_eWrap` and `eWrap_zero`) identifies the DLN loss RLCT with the core-loss RLCT
`rlctAt (∑(coreGen dvec eWrap)ᵢ²) 0`, which the V-lower headline caps below by `4`. -/
theorem dln_rlct334_ge_four :
    (4 : ℝ) ≤ RLCT.Global.rlctGlobal
      (lossDLN dvec (0 : Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℝ)) := by
  have hred := coreReduction dvec (by norm_num : (0 : ℕ) < 2) eWrap measurePreserving_eWrap eWrap_zero
  rw [hred]
  exact OverVanishHeadline334.rlctAt_coreGen334_ge_four

end DLNFibre.DLN.Aoyagi
