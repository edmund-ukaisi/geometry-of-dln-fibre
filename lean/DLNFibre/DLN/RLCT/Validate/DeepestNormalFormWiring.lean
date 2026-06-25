import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestNormalFormWiring` — the L2 normal-form CONVERGENCE node, pre-staged

The Skeleton `deepest_regular_core_normal_form` (the **value-form** of the L2 reduction) is the
convergence node of the λ-spine (the #40 audit): it is **not** closeable by L2 alone — it needs the
L2 chart geometry AND R1's value composed. This module pre-stages that wiring as a CONDITIONAL lemma
taking the two gates as explicit hypotheses, so when the gates land the Skeleton sorry is a one-line
fill (`exact deepest_normal_form_of_value …`), with the convergence already de-risked + audited green.

The two inputs (both named, neither glossed):

- **`hGne`** — the reduced-core germ-nonvanishing carve-out. Feeds the VALUE-FREE reduction
  `deepest_regular_core_reduces` (`DeepestGaugeChart`, itself sorry-free modulo the L2 chart existence
  `deepest_gauge_squeeze_exists` = cobuild-sub34's regAbsorb instance), which lands
  `rlctAt H (dlnLoss H B) deepestPoint = nReg/2 + rlctAtOn(dlnLoss M 0) 0` (core RLCT, NOT `lambdaCore`).
  `hGne` holds for the non-degenerate reduced chain (no interior `M_s = 0`, crux2 #65's
  `dlnLoss_deepest_core_ae_ne_zero`); the degenerate boundary is the separate #70 direct-Morse lemma.
- **`hRValue`** — R1's value `rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)` (= `resolution_charts`
  ▸ A1 `lambdaCore_eq_clean`; cover wires the Skeleton `resolution_charts`, A1 supplies the value
  step). This is the singular-core resolution value — the geometric content of R1, kept SEPARATE from
  the L2 chart fact (the #40-audit scope split).

The conclusion is the Skeleton `deepest_regular_core_normal_form` value-form verbatim:
`rlctAt H (dlnLoss H B) deepestPoint = nReg/2 + ofReal(lambdaCore M)`. Proof = the value-free
reduction (consuming `hGne`) rewritten by `hRValue`. **Gate-independent**: this lemma's OWN proof is
closeable now (the two gates are hypotheses, not sorries) — only its eventual USE in Skeleton awaits the
gates discharging. `M = fun s => H s - r` throughout (the reduced widths).
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The L2 normal-form WIRING (the convergence node, pre-staged).** Given the reduced-core
germ-nonvanishing `hGne` (⟹ the value-free L2 reduction applies) and R1's resolution value `hRValue`
(`rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)`), the local RLCT at the deepest point IS the
closed-form value `nReg/2 + ofReal(lambdaCore M)` — the Skeleton `deepest_regular_core_normal_form`
target. Proof: `deepest_regular_core_reduces` (value-free, `nReg/2 + rlctAtOn(core) 0`) ▸ `hRValue`.

This is the assembly seam where the L2 chart geometry (#59, via `deepest_regular_core_reduces`) and
R1's value (#39 ▸ A1, via `hRValue`) MEET to produce the value-form. Pre-staged so the Skeleton sorry
at `deepest_regular_core_normal_form` collapses to `exact deepest_normal_form_of_value … hGne hRValue`
once both gates land. -/
theorem deepest_normal_form_of_value (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
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
  rw [deepest_regular_core_reduces H r B hB hr hL hGne, hRValue]

end DLNFibre.DLN.RLCT
