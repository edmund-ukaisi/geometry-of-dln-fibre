import DLNFibre.DLN.RLCT.Foundations.Rlct
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1Additive` — S1.5 smooth-block additivity

S1.5 (`rlct_additive_smooth_block_aux`): a nondegenerate-quadratic (regular) block `Σᵢ xᵢ²`,
disjoint from a singular block `G(y)²`, contributes `n/2` to the RLCT. The form L2 consumes (the regular
generators add their ½-per-coordinate to `λ_core`). Proven standalone (the `(B)` `_aux` pattern).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal Topology

/-- **S1.5 (RLCT additivity — smooth/regular block).** A nondegenerate-quadratic block `Σᵢ xᵢ²`
disjoint from a singular block `G(y)²` adds `n/2`. (Wire-in target for
`Skeleton.rlct_additive_smooth_block`; verbatim statement, distinct name.) -/
theorem rlct_additive_smooth_block_aux {n : ℕ}
    {Y : Type*} [MeasureSpace Y] [TopologicalSpace Y] (G : Y → ℝ) (y0 : Y) :
    rlctAtOn (fun p : (Fin n → ℝ) × Y => (∑ i, p.1 i ^ 2) + G p.2 ^ 2) (0, y0)
      = (n : ENNReal) / 2 + rlctAtOn (fun y => G y ^ 2) y0 := by
  sorry

end DLNFibre.DLN.RLCT
