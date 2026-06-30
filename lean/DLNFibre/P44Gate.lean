import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Validate.DeepestL2Wiring
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart

/-!
# `P44Gate` — SCRATCH directed-exact gate: the EXACT residual of Skeleton #44 at L = 2

NOT canonical, NOT imported by `DLNFibre.lean`. Scratch on `genm-p44c` to PIN the minimal residual
hypothesis set for `deepest_regular_core_normal_form` (Skeleton #44) at `L = 2`, by chaining the
PROVEN `deepest_regular_core_normal_form_of` (DeepestL2Wiring) — which itself routes through
`deepest_regular_core_reduces` → the gauge chart `deepest_gauge_chart_construct`. The leaf hypotheses
are explicit `sorry` stubs; the gate compiles iff the chain is exactly the residual.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-- **The directed-exact gate.** Skeleton #44 conclusion at `L = 2`, chained from the proven
`deepest_regular_core_normal_form_of`. The residual = exactly `{hcore, hGne}` (the `_of` hyps); the
gauge chart (consumed inside `deepest_regular_core_reduces`) is built clean-three at L = 2 via
`deepest_gauge_chart_construct` from `{hL2, hpos, hJfront (#100), htop (#154)}`. This gate makes the
FOUR residual leaves explicit as `sorry` stubs and confirms the chain typechecks. -/
theorem p44_at_L2_residual_gate (H : Fin (2 + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (2 + 1), r ≤ H s) (hpos : ∀ s : Fin (2 + 1), r < H s) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr (by norm_num))
      = ((r * (H 0 + H (Fin.last 2) - r) : ℕ) : ℝ≥0∞) / 2
        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
  -- LEAF 1 — hcore: R1 core-value (R1/detfderiv lane; PIN, do not dive).
  have hcore : rlctAtOn
      (fun A : Params (fun s => H s - r) =>
        dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last 2))) ℝ) A)
      (fun _ => 0 : Params (fun s => H s - r))
      = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
    sorry
  -- LEAF 2 — hGne: reduced-core germ-nonvanishing (measure-theory).
  have hGne : ∃ U ∈ 𝓝 (0 : Fin (flatDim (fun s => H s - r)) → ℝ),
      ∀ᵐ z ∂(volume.restrict U),
        dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last 2))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm z) ≠ 0 := by
    sorry
  exact deepest_regular_core_normal_form_of H r B hB hr (by norm_num) hcore hGne

/-- **The gauge-chart-existence residual** (the OTHER half — what `deepest_regular_core_reduces`
consumes inside `_of`, currently the bare `:357` stub). At L = 2 it's `deepest_gauge_chart_construct`
from `{hJfront (#100 col-WLOG), htop (#154 row-WLOG)}` (hL2/hpos free at L=2). This gate pins those
two leaves. -/
theorem p44c_gauge_chart_residual_gate (H : Fin (2 + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (2 + 1), r ≤ H s) (hpos : ∀ s : Fin (2 + 1), r < H s) :
    Nonempty (DeepestGaugeChart H r B hB hr (by norm_num)) := by
  -- LEAF 3 — hJfront: front-pivot col-WLOG (#100, banked; or B·Π transfer).
  have hJfront : ((deepestPoint_frame_pivot_exists H r B hB hr (by norm_num) (by norm_num)).choose).trans
      (finCongr (H_lastLayer_succ H (by norm_num))).toEmbedding = frontEmbed H r hr := by
    sorry
  -- LEAF 4 — htop: row-alignment row-WLOG (#154, banked; or B·Π transfer).
  have htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
      (id : Fin (H (Fin.last 2)) → Fin (H (Fin.last 2)))).rank = r := by
    sorry
  exact deepest_gauge_chart_construct H r B hB hr (by norm_num) (by norm_num) hpos hJfront htop

end DLNFibre.DLN.RLCT
