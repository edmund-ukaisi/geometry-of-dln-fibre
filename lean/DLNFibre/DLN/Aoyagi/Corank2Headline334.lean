import DLNFibre.Core.Aoyagi.SandwichCoverValue
import DLNFibre.DLN.Aoyagi.Corank2Chart334

/-!
# `DLN.Aoyagi.Corank2Headline334` — the (3,3,4) V-lower headline reduction (sorry-free)

The (3,3,4) value headline `4 ≤ rlctAt (∑(coreGen dvec eWrap)ᵢ²) 0` reduced to the ONE substantive
geometric input the born-α seat owes: a resolution chart FAMILY over the deepest point carrying the
area-formula data + the born-α SUM-level sandwich + the a.e.-cover, together with the divisor value
`divisorMin = 8` (Object D, `minAdm ![3,3,4] = 8`). Everything the family does NOT touch is discharged
here concretely:

* **`hFmeas`** — the loss components are measurable (`chart334.hFmeas`, `coreGen` continuous);
* **`hbdd`** (the genuine pole at `0`, = V-upper #110) — `BddAbove (localAdmissibleExponents …)` from
  the single certified `chart334` (`bddAbove_localAdmissible_coreGen334` below): the sandwich is a
  LOWER bound only, so without `hbdd` `⨅ threshold ≤ 0` and the headline is false — this is exactly
  the V-upper content, taken here from one chart (no atlas/cover);
* the STEP 4→5 value normalisation `⨅ monomialThreshold → ½·divisorMin` (`SandwichCoverValue`
  joint, under unit divisor multiplicity `hunit_mult`) and the arithmetic `½·8 = 4`.

So the reduction packages the V-lower spine (wire → joint → value read-off) into ONE contract: build
the born-α family (the surfaced seat) + `divisorMin = 8`, get the headline. NO born-α content is
proved here — `hsandwich`/`hjac`/`hcover` are HYPOTHESES (the family the seat constructs), NOT charts.

## Scope (honest)
- IN: the headline `4 ≤ rlctAt` from the wire's per-chart family hypotheses + `divisorMin = 8`, with
  `hFmeas`/`hbdd`/joint/arithmetic discharged concretely for `coreGen dvec eWrap` at `0`. Sorry-free.
- OUT: the born-α family construction (the gWrapFan leaf charts + the ×6 born-α pullback `hpull`
  feeding `DomainSandwich.sandwich_on_domain_of_survivor`, the per-leaf `jac`, the box-inflation
  cover) — the dedicated seat. This module is the reduction that seat plugs into.
-/

open MeasureTheory Set Filter Topology
open DLNFibre.Core.Aoyagi RLCT
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi

/-- **`hbdd` for the (3,3,4) core loss at `0`, from the single chart** (the V-upper #110 content).
`BddAbove (localAdmissibleExponents (∑(coreGen dvec eWrap)ᵢ²) 0)`: the local admissible exponents of
the loss inject (via `chart334`'s change-of-variables leg
`Chart.mem_wLocalAdmissible_of_localAdmissible`) into the chart's WEIGHTED admissible set, which is a
half-open interval `Ico 0 (monomialThreshold …)` (`Chart.wLocalAdmissibleExponents_eq_Ico`), hence
bounded above. This is the genuine-pole guard the V-lower wire needs (`rlctAt_ge_…_of_sandwich_cover`'s
`hbdd`); it is the elementary single-chart upper direction, no atlas/cover/`θ`. -/
theorem bddAbove_localAdmissible_coreGen334 :
    BddAbove (localAdmissibleExponents (sumSqFam (coreGen dvec eWrap)) (0 : Fin 21 → ℝ)) := by
  have hincl : localAdmissibleExponents (sumSqFam (coreGen dvec eWrap)) (0 : Fin 21 → ℝ) ⊆
      wLocalAdmissibleExponents chart334.jacWeightFn
        (sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ chart334.g)) 0 :=
    fun cc hcc ↦ chart334.mem_wLocalAdmissible_of_localAdmissible hcc
  have hbdd : BddAbove (wLocalAdmissibleExponents chart334.jacWeightFn
      (sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ chart334.g)) 0) := by
    rw [chart334.wLocalAdmissibleExponents_eq_Ico]; exact bddAbove_Ico
  exact hbdd.mono hincl

/-- **The (3,3,4) V-lower headline, reduced to the born-α family + `divisorMin = 8`.** Given a finite
resolution-chart family `g c` over compact domains `dom c` whose images a.e.-cover a neighbourhood `U`
of `0` (`hcover`), each carrying the area-formula data (differentiable, `dom c ⊆ nbhd c` open,
a.e.-injective off a null `excep c`, Jacobian normal form `|det Dg| = jacWeight (jac c) · |unit c|`),
the constant-survivor divisibility chain `hchain`, and the SUM-level born-α SANDWICH
`cst c · ∑ₖ (monomialₖ)² ≤ ∑ᵢ (coreGenᵢ ∘ g c)²` near each point of `dom c` — and the divisor value
`divisorMin = ⨅_c ⨅_{binding} (jac_c d + 1) = 8` (Object D) with unit binding multiplicity
`hunit_mult` — the RLCT of the (3,3,4) core loss at the deepest point is `≥ 4`.

Composition: the abstract V-lower wire (`rlctAt_ge_iInf_threshold_of_sandwich_cover`, `hFmeas`/`hbdd`
supplied concretely) gives `⨅_c monomialThreshold ≤ rlctAt`; the STEP 4→5 joint
(`rlctAt_ge_half_divisorMin_of_iInf_threshold`, under `hunit_mult`) normalises it to
`½·divisorMin ≤ rlctAt`; and `divisorMin = 8` reads off `4 ≤ rlctAt`
(`rlctAt_ge_four_of_half_divisorMin`). The born-α content (`hsandwich`) is a HYPOTHESIS — the seat's
work — not proved here. -/
theorem rlctAt_coreGen334_ge_four_of_family
    {numCharts : ℕ} (hne : (Finset.univ : Finset (Fin numCharts)).Nonempty)
    (g : Fin numCharts → (Fin 21 → ℝ) → (Fin 21 → ℝ))
    (dom nbhd excep : Fin numCharts → Set (Fin 21 → ℝ))
    (bexp : Fin numCharts → Fin (dvec (Fin.last 2) * dvec 0) → Fin 21 → ℕ)
    (k₀ : Fin numCharts → Fin (dvec (Fin.last 2) * dvec 0))
    (jac : Fin numCharts → Fin 21 → ℕ) (unit : Fin numCharts → (Fin 21 → ℝ) → ℝ)
    (cst : Fin numCharts → ℝ) (U : Set (Fin 21 → ℝ))
    (hbind : ∀ c, (bindingAxes (bexp c (k₀ c))).Nonempty)
    (hgdiff : ∀ c, Differentiable ℝ (g c))
    (hdomcpt : ∀ c, IsCompact (dom c))
    (hnbhd_open : ∀ c, IsOpen (nbhd c)) (hdom_sub : ∀ c, dom c ⊆ nbhd c)
    (hexcep_meas : ∀ c, MeasurableSet (excep c)) (hexcep_null : ∀ c, volume (excep c) = 0)
    (hg_inj : ∀ c, Set.InjOn (g c) (nbhd c \ excep c))
    (hchain : ∀ c k d, bexp c (k₀ c) d ≤ bexp c k d)
    (hunit_cont : ∀ c, ContinuousOn (unit c) (nbhd c))
    (hunit_ne : ∀ c, ∀ u ∈ nbhd c, unit c u ≠ 0)
    (hjac : ∀ c, ∀ u ∈ nbhd c, |jacDet (g c) u| = jacWeight (jac c) u * |unit c u|)
    (hcst : ∀ c, 0 < cst c)
    (hsandwich : ∀ c, ∀ p ∈ dom c, ∀ᶠ w in 𝓝 p,
      0 ≤ cst c * sumSqFam (monomialFam (bexp c)) w ∧
        cst c * sumSqFam (monomialFam (bexp c)) w
          ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ g c) w)
    (hU : U ∈ 𝓝 (0 : Fin 21 → ℝ))
    (hcover : volume (U \ ⋃ c, g c '' dom c) = 0)
    (hunit_mult : ∀ c, ∀ d ∈ bindingAxes (bexp c (k₀ c)), bexp c (k₀ c) d = 1)
    (hdivisorMin : Finset.univ.inf' hne
        (fun c ↦ (bindingAxes (bexp c (k₀ c))).inf' (hbind c) (fun d ↦ (jac c d + 1 : ℝ))) = 8) :
    (4 : ℝ) ≤ rlctAt (sumSqFam (coreGen dvec eWrap)) (0 : Fin 21 → ℝ) := by
  have hFmeas : ∀ i, Measurable (coreGen dvec eWrap i) := chart334.hFmeas
  have hbdd := bddAbove_localAdmissible_coreGen334
  have hwire := rlctAt_ge_iInf_threshold_of_sandwich_cover hne g dom nbhd excep bexp k₀ jac unit cst U
    hbind hFmeas hgdiff hdomcpt hnbhd_open hdom_sub hexcep_meas hexcep_null hg_inj hchain
    hunit_cont hunit_ne hjac hcst hsandwich hU hcover hbdd
  have hjoint := rlctAt_ge_half_divisorMin_of_iInf_threshold hne bexp k₀ jac hbind hunit_mult hwire
  exact rlctAt_ge_four_of_half_divisorMin hdivisorMin hjoint

-- Forced axiom gate: the hbdd brick + the headline reduction rest only on
-- `[propext, Classical.choice, Quot.sound]` (no born-α content is proved here).
#assert_banked_clean_batch [bddAbove_localAdmissible_coreGen334, rlctAt_coreGen334_ge_four_of_family]

end DLNFibre.DLN.Aoyagi
