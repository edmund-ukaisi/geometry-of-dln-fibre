import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction
import DLNFibre.DLN.RLCT.Validate.DeepestL2Wiring
import DLNFibre.DLN.RLCT.Validate.DeepestNormalFormWiring

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestNormalFormFrontPivot` — L2 normal-form chain at front-pivot `B`

The KC2 front-pivot restatement of the L2 value-free reduction chain. The general-`B`
`deepest_gauge_squeeze_exists` (`DeepestGaugeChart`) is a bare `sorry`: its only producer
`deepest_gauge_chart_construct` (`DeepestGaugeConstruction`) needs the front-pivot hypothesis
`hJfront` (the deepest point's last-layer pivot embedding is the front embedding `k ↦ k`), which a
GENERAL `B` does not supply. The WLOG move is to run the chart only at a front-pivot target `Bp`
(the headline ⨅-level column-permutation reduction `headline_frontPivot_exists`, KC2 ⨅-wire), where
`hJfront` is available.

This module carries that chain at front-pivot `B`, threading `hJfront` (+ `2 ≤ L`, `hpos`) as
explicit hypotheses — so it is `sorry`-free, and the `hJfront` discharge is deferred to the
deepest-point front-alignment (KC1). The three theorems mirror the general-`B` originals verbatim
except they obtain the gauge chart from `deepest_gauge_chart_construct` (front-pivot) rather than
the bare-`sorry` `deepest_gauge_squeeze_exists`:

- `deepest_gauge_squeeze_exists_frontPivot` — chart-existence, now PROVEN (front-pivot producer).
- `deepest_regular_core_reduces_frontPivot` — the value-free reduction
  (= `deepest_regular_core_reduces` but consuming the front-pivot chart).
- `deepest_normal_form_of_value_frontPivot` — the convergence node (= `deepest_normal_form_of_value`
  but consuming the front-pivot reduction).

`M = fun s => H s - r` throughout (the reduced widths). The controller wires these into the
canonical headline (`aoyagi_learning_coefficient`) via `headline_frontPivot_exists`, with `hJfront`
discharged by the strengthened (alignment-parametric) `deepestPoint_exists` (KC1).
-/

open MeasureTheory
open scoped ENNReal Topology

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The gauge-slice squeeze datum at front-pivot `B`** (KC2). The chart exists when the deepest
point's last-layer pivot embedding is the front embedding (`hJfront`) — via the banked producer
`deepest_gauge_chart_construct`, replacing the general-`B` bare-`sorry`
`deepest_gauge_squeeze_exists`.
Threads `2 ≤ L` (distinct boundary layers) and `hpos` (strict reduced widths), which the producer
needs. -/
theorem deepest_gauge_squeeze_exists_frontPivot (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (hJfront : ((deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose).trans
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr) :
    Nonempty (DeepestGaugeChart H r B hB hr hL) :=
  deepest_gauge_chart_construct H r B hB hr hL hL2 hpos hJfront

/-- **The VALUE-FREE L2 reduction at front-pivot `B`** (KC2). Mirrors `deepest_regular_core_reduces`
verbatim, but obtains the gauge chart from the front-pivot producer
`deepest_gauge_squeeze_exists_frontPivot` (so it is `sorry`-free modulo the threaded `hJfront`). The
local RLCT of `dlnLoss H B` at the deepest point splits as the regular gauge shift `nReg/2` plus the
reduced singular core RLCT `rlctAtOn (dlnLoss M 0) 0`. -/
theorem deepest_regular_core_reduces_frontPivot (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (hJfront : ((deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose).trans
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr)
    (hGne : ∃ U ∈ 𝓝 (0 : Fin (flatDim (fun s => H s - r)) → ℝ),
      ∀ᵐ z ∂(volume.restrict U),
        dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm z) ≠ 0) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = ((r * (H 0 + H (Fin.last L) - r) : ℕ) : ℝ≥0∞) / 2
        + rlctAtOn
            (fun A : Params (fun s => H s - r) =>
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
            (fun _ => 0 : Params (fun s => H s - r)) := by
  obtain ⟨Γ⟩ := deepest_gauge_squeeze_exists_frontPivot H r B hB hr hL hL2 hpos hJfront
  rw [deepest_squeeze_transport H r B hB hr hL Γ,
    deepest_regular_smooth_split H r B hB hr hL Γ hGne]

/-- **The L2 normal-form WIRING at front-pivot `B`** (KC2, the convergence node). Mirrors
`deepest_normal_form_of_value` but consumes the front-pivot reduction
`deepest_regular_core_reduces_frontPivot`. Given the reduced-core germ-nonvanishing `hGne` and R1's
resolution value `hRValue`, the local RLCT at the deepest point is the closed form
`nReg/2 + ofReal(lambdaCore M)` — the Skeleton `deepest_regular_core_normal_form` target. -/
theorem deepest_normal_form_of_value_frontPivot (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (hJfront : ((deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose).trans
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr)
    (hGne : ∃ U ∈ 𝓝 (0 : Fin (flatDim (fun s => H s - r)) → ℝ),
      ∀ᵐ z ∂(volume.restrict U),
        dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm z) ≠ 0)
    (hRValue :
      rlctAtOn
          (fun A : Params (fun s => H s - r) =>
            dlnLoss (fun s => H s - r)
              (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
          (fun _ => 0 : Params (fun s => H s - r))
        = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = ((r * (H 0 + H (Fin.last L) - r) : ℕ) : ℝ≥0∞) / 2
        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
  rw [deepest_regular_core_reduces_frontPivot H r B hB hr hL hL2 hpos hJfront hGne, hRValue]

/-- **The headline learning coefficient at front-pivot `B`** (KC2 capstone). For a front-pivot target
(`hJfront`), with the reduced-core germ-nonvanishing `hGne`, R1's resolution value `hRValue`, the
`D1` ≥-leg `hD1` (`⨅ = rlctAt deepestPoint`), and the strict-width `hpos`/`2 ≤ L`, the global learning
coefficient infimum equals Aoyagi's closed form. This is `aoyagi_learning_coefficient` specialised to
a front-pivot `B`: `D1` (→ deepest point, via `hD1`) ▸ the front-pivot L2 normal form
(`deepest_normal_form_of_value_frontPivot`) ▸ the closed-form recombination
(`reg_shift_add_core_eq_aoyagiLambda`). The general-`B` headline follows by the ⨅-level column-perm
WLOG (`headline_frontPivot_exists`); `hJfront`/`hRValue`/`hD1`/`hGne` are discharged downstream
(KC1 / R1 / the D1 ≥-leg). -/
theorem aoyagi_learning_coefficient_frontPivot (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (hJfront : ((deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose).trans
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr)
    (hGne : ∃ U ∈ 𝓝 (0 : Fin (flatDim (fun s => H s - r)) → ℝ),
      ∀ᵐ z ∂(volume.restrict U),
        dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm z) ≠ 0)
    (hRValue :
      rlctAtOn
          (fun A : Params (fun s => H s - r) =>
            dlnLoss (fun s => H s - r)
              (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
          (fun _ => 0 : Params (fun s => H s - r))
        = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
    (hD1 : (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w)
        = rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) := by
  rw [hD1, deepest_normal_form_of_value_frontPivot H r B hB hr hL hL2 hpos hJfront hGne hRValue,
    reg_shift_add_core_eq_aoyagiLambda H r hr hL]

end DLNFibre.DLN.RLCT
