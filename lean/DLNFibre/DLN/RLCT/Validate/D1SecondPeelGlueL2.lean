import DLNFibre.DLN.RLCT.Validate.D1SecondPeelAssembly
import DLNFibre.DLN.RLCT.Validate.D1SecondPeelMinor

/-!
# `DLNFibre.DLN.RLCT.Validate.D1SecondPeelGlueL2` — the L = 2 D1 `≥`-leg glue (Skeleton reduction)

The standalone L = 2 glue lemma the controller wires into the bare general-L Skeleton `sorry`
`rlctAt_deepest_le_of_optimal` (`Skeleton.lean:1172`). It reduces the L = 2 specialisation of that
goal — `rlctAt (deepestPoint H r B …) ≤ rlctAt v` at a middle-stratum optimal `v` — to the more-
assembled Route A producer `deepest_le_of_optimal_secondPeel_discharged` (`D1SecondPeelAssembly`),
threading its named hypotheses and DISCHARGING the second-peel minor non-degeneracy `hminor₂` from a
RANK lower bound on the slice residual's Jacobian (`exists_secondPeel_minor`, `D1SecondPeelMinor`).

## The legible two-gate shape (the precision win)

The bare Skeleton `sorry` becomes a reduction whose remaining debt is exactly TWO NAMED-OPEN gated
hypotheses, each with its tracked producer:

  * **`hDeepest`** = #44 (`deepest_regular_core_normal_form` at the L = 2 `deepestPoint`, in the
    Route-A `nReg/2 + coreDeepest` form) — ← the open #149/#153 `deepest_diffeo_bridge_L2` wiring.
  * **`hInterface`** = `R1ResolutionInterface` at the degraded core `M'` (← R1-LOWER
    `cover_ge_div`).

Everything ELSE is either threaded per-`v` analytic data (the first-peel `C¹` residual `q` + its
chart transfer `hchart`, the second-peel slice `C²`-ness + the rank bound) or DISCHARGED here:
`hminor₂` from the rank bound `hrank₂` via the network-free `exists_secondPeel_minor`.

The first-peel `hchart`/`q` is itself producible sorry-free (`dln_hchart_residual` +
`exists_jacFlatL2_minor`, both banked at canonical) at a general optimal `v`; it is threaded as a
hypothesis here rather than inlined, to keep the glue a thin, legible reduction (the controller —
or a follow-on tide — inlines the first-peel producer when the middle-stratum `(m,a,b)` extraction
at a general `v` is settled).

Scope L = 2 only (`H : Fin 3 → ℕ`). The general-L Skeleton `sorry` stays #120-walled — NOT touched.
This file does NOT edit `Skeleton.lean`; the controller wires `rlctAt_deepest_le_of_optimal_L2` in.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-- **The L = 2 D1 per-point `≥`-leg, Skeleton form, with `hminor₂` discharged from a rank bound.**

At a middle-stratum optimal `v` (square deepest reduced widths `(m,m,m)`, `a + b ≤ m`), with the
deepest point `deepest := deepestPoint H r B hB hr hL`, this concludes the Skeleton per-point goal

    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) ≤ rlctAt H (dlnLoss H B) v

from:
  * the FIRST-peel `C¹` residual `q` + chart transfer `hchart` + slice non-vanishing `hRne` (the
    `dln_hchart_residual` output at `v`; threaded);
  * the SECOND-peel slice `C²`-ness `hslice` + vanishing `hslice0`, and the RANK lower bound
    `hrank₂ : extraCount m a b ≤ (jacResid (q (0,·)) t0).rank` — from which `hminor₂` (and its
    selectors `eh, ec`) are BUILT via `exists_secondPeel_minor` (no longer a hypothesis);
  * the two NAMED-OPEN gates `hDeepest` (#44, Route-A form) and `hInterface`
    (`R1ResolutionInterface`).

`nReg = nRegL2 H r`, `extra = extraCount m a b`, `Nslice` the first-peel complement dimension,
`coreDeepest = ofReal(lambdaCore (square m))`. -/
theorem rlctAt_deepest_le_of_optimal_L2 {Nslice n : ℕ}
    (H : Fin (2 + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (hB : B.rank = r) (hr : ∀ s : Fin (2 + 1), r ≤ H s) (hL : 1 ≤ 2)
    (v : Params H) (m a b : ℕ) (hab : a + b ≤ m) (coreDeepest : ℝ≥0∞)
    (hcoreDeepest : coreDeepest = ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ))
    -- GATE 1 (#44): the deepest-side equality at the constructed `deepestPoint`, Route-A form
    (hDeepest : rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
        = (nRegL2 H r : ℝ≥0∞) / 2 + coreDeepest)
    -- FIRST-peel `C¹` residual + chart transfer (the `dln_hchart_residual` output at `v`)
    (q : (Fin (nRegL2 H r) → ℝ) × (Fin Nslice → ℝ) → EuclideanSpace ℝ (Fin n))
    (hq : ContDiff ℝ 1 q) (t0 : Fin Nslice → ℝ)
    (hchart : rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × (Fin Nslice → ℝ) =>
            (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) ((0 : Fin (nRegL2 H r) → ℝ), t0))
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
        (∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), z) i ^ 2) ≠ 0)
    -- SECOND-peel slice data: `C²` + vanishing + the RANK bound (discharges `hminor₂` + selectors)
    (hslice : ContDiff ℝ 2 (fun t : Fin Nslice → ℝ => q ((0 : Fin (nRegL2 H r) → ℝ), t)))
    (hslice0 : (fun t : Fin Nslice → ℝ => q ((0 : Fin (nRegL2 H r) → ℝ), t)) t0 = 0)
    (hrank₂ : extraCount m a b
        ≤ (jacResid (fun t : Fin Nslice → ℝ => q ((0 : Fin (nRegL2 H r) → ℝ), t)) t0).rank)
    -- GATE 2 (R1): the §5 R1-resolution interface at the degraded core `M'` (the same shape Route A
    -- consumes, with the BUILT second-peel residual `q₂`/`t0₂`)
    (hInterface : ∀ (q₂ : (Fin (extraCount m a b) → ℝ) × (Fin (Nslice - extraCount m a b) → ℝ)
          → EuclideanSpace ℝ (Fin n)) (t0₂ : Fin (Nslice - extraCount m a b) → ℝ),
        (rlctAtOn (fun t : Fin Nslice → ℝ => ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0
            = rlctAtOn
                (fun p : (Fin (extraCount m a b) → ℝ) × (Fin (Nslice - extraCount m a b) → ℝ) =>
                  (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2)) ((0 : Fin (extraCount m a b) → ℝ), t0₂)) →
        (∃ U ∈ 𝓝 t0₂, ∀ᵐ z ∂(volume.restrict U),
            (∑ i, q₂ ((0 : Fin (extraCount m a b) → ℝ), z) i ^ 2) ≠ 0)
          ∧ rlctAtOn (fun t : Fin (Nslice - extraCount m a b) → ℝ =>
              ∑ i, q₂ ((0 : Fin (extraCount m a b) → ℝ), t) i ^ 2) t0₂
            = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) ≤ rlctAt H (dlnLoss H B) v := by
  -- DISCHARGE the second-peel minor `hminor₂` + its selectors from the rank bound.
  obtain ⟨eh, ec, heh, hec, hminor₂⟩ :=
    exists_secondPeel_minor (fun t : Fin Nslice → ℝ => q ((0 : Fin (nRegL2 H r) → ℝ), t)) t0 hrank₂
  -- reduce to Route A (the producer that BUILDS the second-peel chart from `hminor₂`).
  exact deepest_le_of_optimal_secondPeel_discharged H r B (deepestPoint H r B hB hr hL) v m a b hab
    coreDeepest hcoreDeepest hDeepest q hq t0 hchart hRne hslice hslice0 eh ec heh hec hminor₂
    hInterface

end DLNFibre.DLN.RLCT
