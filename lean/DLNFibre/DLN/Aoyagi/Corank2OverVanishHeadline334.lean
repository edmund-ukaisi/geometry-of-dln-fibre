import DLNFibre.DLN.Aoyagi.Corank2FoldedFamily334

/-!
# `DLN.Aoyagi.Corank2OverVanishHeadline334` — the UNCONDITIONAL (3,3,4) V-lower headline

The convergence deliverable of the expedition: the hypothesis-free, cite-free, monument-free

`rlctAt_coreGen334_ge_four : (4:ℝ) ≤ rlctAt (sumSqFam (coreGen dvec eWrap)) 0`.

It applies the STEP-6 spine `OverVanishAssembly334.rlctAt_coreGen334_ge_four_of_perchart_integrable`
to the folded chart family `gFold` (`Corank2FoldedFamily334`). The DONE spine obligations (`hgdiff`,
`hcover`, `hexcep_*`, compactness) come from the foundation; the two remaining holes are:

* `hg_inj` (ainj) — the folded chart is a.e.-injective off its critical set `excepFold c`;
* `hint` (over-vanishing) — the weighted pulled-back loss is integrable near each base point.

These are proved in sibling files against the `Corank2FoldedFamily334` foundation and wired here.

## Status
SKELETON — statement locked; spine composition verified. Two tracked frontier holes
(`-- map: ov-headline-ainj`, `-- map: ov-headline-hint`); NOT yet axiom-clean.
-/

open MeasureTheory Set Filter Topology Metric RLCT
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi.OverVanishHeadline334

/-- **The UNCONDITIONAL (3,3,4) V-lower headline** (Approach B, folded chart). Hypothesis-free,
cite-free, monument-free: `4 ≤ rlctAt` of the `(3,3,4)` core loss at `0`. Applies the STEP-6 spine to
the folded family `gFold` over the inflated leaf box `domFold`. -/
theorem rlctAt_coreGen334_ge_four :
    (4 : ℝ) ≤ rlctAt (sumSqFam (coreGen dvec eWrap)) (0 : Fin 21 → ℝ) := by
  refine OverVanishAssembly334.rlctAt_coreGen334_ge_four_of_perchart_integrable
    (numCharts := numCharts) ⟨⟨0, numCharts_pos⟩, Finset.mem_univ _⟩
    gFold domFold nbhdFold excepFold
    ?hgdiff isCompact_domFold isOpen_nbhdFold domFold_sub
    measurableSet_excepFold volume_excepFold ?hg_inj ?hcover ?hint
  case hgdiff => exact differentiable_gFold
  case hg_inj =>
    -- map: ov-headline-ainj — folded chart a.e.-injectivity off its critical set.
    sorry
  case hcover => exact folded_hcover
  case hint =>
    -- map: ov-headline-hint — per-chart integrability: clean (b) / over-vanishing (c).
    sorry

end DLNFibre.DLN.Aoyagi.OverVanishHeadline334
