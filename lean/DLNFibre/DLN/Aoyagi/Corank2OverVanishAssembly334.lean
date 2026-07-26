import DLNFibre.DLN.Aoyagi.Corank2Headline334
import DLNFibre.DLN.Aoyagi.Corank2OverVanish334

/-!
# `DLN.Aoyagi.Corank2OverVanishAssembly334` — the STEP-6 mechanism-heterogeneous assembly (skeleton)

The convergence point for the full-288 (3,3,4) V-lower headline. The whole-conjugate family covers a
neighbourhood of `0` (`NativeFan334.native_hcover`, transported through the folded `Ψ` on the
over-vanishing leaves via `OverVanish334.image_comp_blockShear_superset`); per chart, the weighted
pulled-back loss `|jacDet g_c| · (∑ᵢ (coreGenᵢ ∘ g_c)²)^{-cc}` is integrable for every `cc < 4`:

* **clean-144** — via the single-entry survivor `hentry` (`coreGen_{k0}∘g_c = ∏ w^{ek₀}`), the chain
  engine `monomialSumSq_integrableAtFilter_of_lt` gives the boxed threshold `≥ 9/2 > 4`;
* **over-vanishing-144** — via `OverVanish334.chart_integrableAtFilter_of_monoSumSq_dom`, the
  product engine gives `min(threshold(vm²), r/2) = 4`.

Both mechanisms produce the SAME per-chart integrability shape, so the assembly abstracts it as ONE
hypothesis `hint` and the two seats discharge it over their charts of the shared cover. With `hbdd`
(the genuine pole, `bddAbove_localAdmissible_coreGen334`) the `Ico 0 4 ⊆ localAdmissible` membership
lifts to `4 ≤ rlctAt`.

## Status
STEP-6 SKELETON (P6): the headline `rlctAt_coreGen334_ge_four_of_perchart_integrable` is
statement-locked; its body is the tracked hole `-- map: step6-assembly` — a refactor of
`Core.Aoyagi.mem_localAdmissible_of_sandwich_lt`'s spine (area formula push-down +
`integrableOn_finite_iUnion` + the `hcover` transfer onto a neighbourhood + `csSup_le_csSup` with
`hbdd`) with the per-chart integrability taken as `hint` rather than derived from a sandwich. To be
filled by the STEP-6 assembler once the per-type facts + Tonelli + clean-144 converge.
-/

open MeasureTheory Set Filter Topology Metric RLCT
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi.OverVanishAssembly334

/-- **STEP 6 (skeleton) — the mechanism-heterogeneous (3,3,4) V-lower headline.** Given a finite
chart family `g` over compact domains `dom` whose images a.e.-cover `ball 0 1` (`hcover`; the
full-288 whole-conjugate cover, `Ψ`-transported on the over-vanishing leaves), each carrying the
area-formula data (differentiable, `dom c ⊆ nbhd c` open, a.e.-injective off a null `excep c`), and
the UNIFORM per-chart per-point integrability `hint` of the weighted pulled-back loss for every
`cc ∈ Ico 0 4` (discharged: clean-144 via the survivor `hentry` → chain engine `≥ 9/2`;
over-vanishing-144 via `chart_integrableAtFilter_of_monoSumSq_dom` → `= 4`), the RLCT of the
`(3,3,4)` core loss at `0` is `≥ 4`. The spine is a refactor of
`mem_localAdmissible_of_sandwich_lt` (per-chart integrability taken as `hint`); `hbdd` =
`bddAbove_localAdmissible_coreGen334`. -/
theorem rlctAt_coreGen334_ge_four_of_perchart_integrable
    {numCharts : ℕ} (_hne : (Finset.univ : Finset (Fin numCharts)).Nonempty)
    (g : Fin numCharts → (Fin 21 → ℝ) → (Fin 21 → ℝ))
    (dom nbhd excep : Fin numCharts → Set (Fin 21 → ℝ))
    (_hgdiff : ∀ c, Differentiable ℝ (g c))
    (_hdomcpt : ∀ c, IsCompact (dom c))
    (_hnbhd_open : ∀ c, IsOpen (nbhd c)) (_hdom_sub : ∀ c, dom c ⊆ nbhd c)
    (_hexcep_meas : ∀ c, MeasurableSet (excep c)) (_hexcep_null : ∀ c, volume (excep c) = 0)
    (_hg_inj : ∀ c, Set.InjOn (g c) (nbhd c \ excep c))
    (_hcover : volume (ball (0 : Fin 21 → ℝ) 1 \ ⋃ c, g c '' dom c) = 0)
    (_hint : ∀ c, ∀ p ∈ dom c, ∀ cc ∈ Set.Ico (0 : ℝ) 4,
      IntegrableAtFilter
        (fun u ↦ |jacDet (g c) u|
          * negPow (sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ g c)) cc u) (𝓝 p)) :
    (4 : ℝ) ≤ rlctAt (sumSqFam (coreGen dvec eWrap)) (0 : Fin 21 → ℝ) := by
  -- map: step6-assembly — refactor of `mem_localAdmissible_of_sandwich_lt`'s spine (area formula +
  -- finite-union subadditivity + `hcover` transfer to `𝓝 0` + `csSup_le_csSup` with `hbdd`), with
  -- per-chart integrability supplied by `hint` (clean-144 hentry / over-vanishing bridge).
  sorry

end DLNFibre.DLN.Aoyagi.OverVanishAssembly334
