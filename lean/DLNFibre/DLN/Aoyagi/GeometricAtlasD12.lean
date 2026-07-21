import DLNFibre.Core.Aoyagi.BlowupResolution
import DLNFibre.DLN.Aoyagi.LearningCoefficient

/-!
# `DLN.Aoyagi.GeometricAtlasD12` — rung (B): the geometric obligation for `d = (1,2)`

WIP toward the FIRST genuine end-to-end discharge of the geometric obligation
`∃ res : Resolution (coreGen d e) 0, AtlasRealizesExponents d res` on a real singular DLN
instance — `d = (1,2)`, `N = 1`. Here `mult` is the single 2×1 layer and `coreGen` is a linear
iso `L` of the two coordinates.

**Blocker found (surfaced to controller).** "Reuse `blowupResolution2` verbatim" is obstructed by a
CARDINALITY MISMATCH: the resolution domain is `Fin (flatDim ![1,2]) → ℝ` and the `F`-index is
`Fin (![1,2] (Fin.last 1) * ![1,2] 0)` — both propositionally `= 2`, but SYNTACTICALLY distinct
from the literal `Fin 2` of `blowupResolution2` (`flatDim` is a `Finset.sum`; M-index a product).
Bridging needs a domain/index-reindex transport (the documented "opaque-width cast" cost). The clean
native path is leaf-2 (a general-`Fin D` origin blow-up) instantiated at `D = flatDim ![1,2]`, whose
one blocker is the general-`D` Jacobian det `w_i^{D-1}`. Banked here: the two `N=1` reductions.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

/-- For `N = 1`, `mult` is the single (last) layer matrix. -/
theorem mult_d12 (A : Tuple (k := ℝ) ![1, 2]) : mult ![1, 2] A = A 0 :=
  Matrix.mul_one (A 0)

/-- `flatDim ![1,2] = 2`. -/
theorem flatDim_d12 : flatDim ![1, 2] = 2 := by decide

end DLNFibre.DLN.Aoyagi
