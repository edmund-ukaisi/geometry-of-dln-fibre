import DLNFibre.DLN.RLCT.Validate.RouteMSchurGeneral
import DLNFibre.DLN.RLCT.Validate.RouteMSchurCorank3

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurRecStep` — the per-corank recStep (R1-UPPER terminal)

The per-corank analytic step `SchurRecStep 4 schurLambda` — the sole remaining input to
`RouteMSchurGeneral.schurGen_lt_top_modulo_recStep`, which it feeds to close the ∀-corank `p = 4`
finiteness (R1-UPPER). Generalises the corank-3 firing (`RouteMSchurCorank3.core_schur3_lt_top`).

## Fidelity check (the shape-pin, validated)
`schurCore4_three` wires the concrete corank-3 instance `core_schur3_lt_top` as `SchurCore 4 3 c' 1`
(the unit-box specialisation of the general predicate). Its compiling confirms the `SchurCore` shape
matches the validated instance — the strongest shape-check.

## Scope (the T-flow verdict, DECISIVE)
`core_schur3_lt_top` is **unit-box (T = 1) only**; the general predicate `SchurCore p r c' T` is
general-`T`. The recStep is proved by the GENERIC per-corank mechanism (radial-Δ cover + N2b split +
shifted-exponent Morse peel + `M22 ↦ Sc` translation + IH), NOT by invoking `core_schur3_lt_top` —
so the T = 1 pin of that endpoint is a property of the validation instance, not an obstruction to the
generic step. The base case (`core_schur2_lt_top`) and the inner engines (`resolvedShiftR2c3_le`,
`resolved334_box_lt_top`, `schurResid2_translate_lt_top`) are all general-`T`/`K`, so the IH is
invocable at the residual radius `≈ T + B` (`B` the Cramer/Schur shift bound). The deferred matrix
`lintegral_comp_smul` box-scaling is needed ONLY to upgrade the standalone `core_schur3_lt_top` to
general-`T`, NOT for the recStep (verdict (A), `codex/genM-recstep-Tscope-answer.md`).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- **Fidelity wire — the corank-3 instance as `SchurCore 4 3` (unit box).** `core_schur3_lt_top`
repackaged as `SchurCore 4 3 c' 1`, confirming the general predicate's shape matches the validated
corank-3 firing (the strongest shape-check). Unit-box only, since `core_schur3_lt_top` is. -/
theorem schurCore4_three (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 4) :
    SchurCore 4 3 c' 1 := by
  simpa only [SchurCore] using core_schur3_lt_top c' hc0 hc'

end DLNFibre.DLN.RLCT
