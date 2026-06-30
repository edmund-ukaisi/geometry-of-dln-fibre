/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreTargetOverlap
import DLNFibre.Core.FibreBundleHeadline
import DLNFibre.Core.RingTheory.Determinantal.LocalTriviality

/-!
# `DLNFibre.Core.FibreZariskiLocalTriviality` — the DLN bundle is a Zariski-locally-trivial affine
product over the rank-`= r` open (P2.d capstone)

The Phase-2 capstone. The abstract predicate
`Algebra.IsZariskiLocallyTrivialAffineProduct` (`Core.RingTheory.Determinantal.LocalTriviality`)
names "locally a product over a principal-open cover of an open `U ⊆ Spec Base`". This module
exhibits the **DLN reduced-fibre bundle** as a genuine (axiom-clean, inhabited) instance of it, over
the rank-`= r` open `rankROpen ⊆ Spec (sweepSigmaRing)`.

## The instance

`reducedFibre_isZariskiLocallyTrivialAffineProduct d r hp hq :
  Algebra.IsZariskiLocallyTrivialAffineProduct k (sweepSigmaRing k d r)
    (SchurLoc ⊗_k sweepFibreRing) SchurLoc (sweepFibreRing) (rankROpen d r)`

with:

* `ι := PivotDatum d r hp hq` (the pivot charts);
* `chart I :=` the `Algebra.AtlasFibreChart` built from the DLN pivot chart — `toAtlasChart :=
  pivotAtlasChart I` (chart element `pivotElt I = chartDsigAt I.s I.t`, bare-`k` trivialization the
  gauge-transported tensor package) and `fibreModel := standardFibreChartOfPivot I` (the over-base
  `≃ₐ[SchurLoc] SchurLoc ⊗_k sweepFibreRing` + flatness);
* `cover :=` the `PivotDatum`-indexed scheme open-cover `iUnion_pivotDatum_basicOpen_eq_rankROpen`
  (the per-pivot charts cover exactly `rankROpen`; the `PivotDatum`-indexed companion of the banked
  selector-indexed `iSup_pivot_basicOpen_eq_rankROpen`).

`pivotElt I = chartDsigAt I.s I.t` definitionally, so the `fibreModel`'s `Total = Away (pivotElt I)`
is the `Away (chartDsigAt I.s I.t)` of `standardFibreChartOfPivot` — the over-base datum slots into
the `AtlasFibreChart` over `pivotAtlasChart`'s chart element with no coercion.

## Inhabitation / satisfiability

Every field of the instance is a banked, machine-checked DLN fact (`pivotAtlasChart`,
`standardFibreChartOfPivot`, `iUnion_pivotDatum_basicOpen_eq_rankROpen`), so the instance is
axiom-clean (`#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`). It is an axiom-clean
**inhabited instance**: the abstract predicate is **satisfiable** by the DLN bundle (its structure
type is inhabited). Nonemptiness of `rankROpen` — that the local triviality is over a *nonempty*
open — is a separate claim, NOT proved here (no `∃ P, P ∈ rankROpen` is exhibited; cf.
`FibreBundleHeadline`'s Witness caveat).

## `name = content`: the open is load-bearing

The instance is over the **open** `rankROpen` (the rank-`= r` locus), NOT over the closure
`Σ̄^r = Spec (sweepSigmaRing)`: a bundle over the closure is FALSE (the rank-`< r` boundary lies in
no chart). The cover hypothesis is `(⋃ I, D((chart I).chartElt)) = rankROpen`, never `= ⊤`.

## What this is NOT

The abstract predicate is the bespoke **Zariski** local-triviality of an affine product — NOT a
Mathlib `FiberBundle` (which is topological: `[TopologicalSpace B]` + local *homeomorphic*
trivializations; there is no algebraic / Zariski local-triviality class at this pin). It packages
the per-chart over-base product + the principal-open cover; the cocycle compatibility holds
automatically (P2.c) and is the derived
`Algebra.IsZariskiLocallyTrivialAffineProduct.overlapTransition_trans_symm`. A single GLOBAL
`Flat π` / triple-overlap coherence + local-to-global flatness assembly stays roadmapped (see
`Core.FibreBundleHeadline`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix
open scoped TensorProduct

variable {k : Type} [Field k] [Infinite k] {N : ℕ}

/-! ## The DLN pivot chart as an abstract `AtlasFibreChart` -/

/-- **The DLN pivot chart as an abstract `Algebra.AtlasFibreChart` (P2.d).** At a pivot `I`, the
abstract chart over the global base `sweepSigmaRing` with standard fibre model `SchurLoc ⊗_k
sweepFibreRing`: its `toAtlasChart` is `pivotAtlasChart I` (chart element `pivotElt I = chartDsigAt
I.s I.t`, bare-`k` trivialization the gauge-transported tensor package), and its over-base
`fibreModel` is `standardFibreChartOfPivot I` (the `≃ₐ[SchurLoc]` local product +
`SchurLoc`-flatness). The `fibreModel`'s `Total = Away (pivotElt I)` is `Away (chartDsigAt I.s I.t)`
definitionally, so the S4b over-base datum slots in with no coercion. -/
noncomputable def pivotAtlasFibreChart (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I : PivotDatum d r hp hq) :
    Algebra.AtlasFibreChart k (sweepSigmaRing k d r)
      (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq)
      (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (sweepFibreRing k d r hp hq) where
  toAtlasChart := pivotAtlasChart d r hp hq I
  fibreModel := standardFibreChartOfPivot d r hp hq I

/-! ## The pivot-indexed scheme cover -/

open PrimeSpectrum in
omit [Infinite k] in
/-- **The `PivotDatum`-indexed scheme cover of the rank-`= r` open.** The per-pivot charts
`basicOpen (chartDsigAt I.s I.t)`, ranging over all `PivotDatum I`, cover exactly `rankROpen`. The
banked cover `iSup_pivot_basicOpen_eq_rankROpen` is indexed over RAW selector pairs `(s, t)`; this
is its `PivotDatum`-indexed companion (the index `AtlasFibreChart` consumers need). Forward: each
`chartDsigAt I.s I.t` is one of the selector charts (`st = (I.s, I.t)`). Backward: a point in
`rankROpen` lies in some selector chart `basicOpen (chartDsigAt s t)`, which
`pivotDatumOfMemBasicOpen` lifts to a `PivotDatum I` with `pivotElt I = chartDsigAt s t`; and
`pivotElt I = chartDsigAt I.s I.t` definitionally, so the point lies in the pivot chart. -/
theorem iUnion_pivotDatum_basicOpen_eq_rankROpen (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (⋃ I : PivotDatum d r hp hq,
        (basicOpen (chartDsigAt (k := k) d r I.s I.t) :
          Set (PrimeSpectrum (sweepSigmaRing k d r))))
      = rankROpen (k := k) d r := by
  apply le_antisymm
  · -- each pivot chart sits inside the selector-indexed cover, which is `rankROpen`.
    rw [← iSup_pivot_basicOpen_eq_rankROpen (k := k) d r]
    refine Set.iUnion_subset (fun I ↦ ?_)
    exact Set.subset_iUnion_of_subset (I.s, I.t) le_rfl
  · -- a point of `rankROpen` is in a selector chart; lift it to a pivot chart.
    rw [← iSup_pivot_basicOpen_eq_rankROpen (k := k) d r]
    refine Set.iUnion_subset (fun st p hp' ↦ ?_)
    rw [SetLike.mem_coe] at hp'
    obtain ⟨I, hI⟩ := pivotDatumOfMemBasicOpen d r hp hq st.1 st.2 hp'
    -- `pivotElt I = chartDsigAt I.s I.t` by `rfl`, and `hI : pivotElt I = chartDsigAt st.1 st.2`.
    have hI' : chartDsigAt (k := k) d r I.s I.t = chartDsigAt d r st.1 st.2 := hI
    refine Set.mem_iUnion.mpr ⟨I, ?_⟩
    rw [SetLike.mem_coe, hI']
    exact hp'

/-! ## The DLN bundle is a Zariski-locally-trivial affine product over the rank-`= r` open -/

/-- **The DLN reduced-fibre bundle is a Zariski-locally-trivial affine product over the rank-`= r`
open (P2.d capstone, inhabited-instance witness).** For a fixed `(d, r)`, the abstract predicate
`Algebra.IsZariskiLocallyTrivialAffineProduct` holds for the DLN reduced-fibre bundle over
`rankROpen d r ⊆ Spec (sweepSigmaRing)`: index type the pivots `PivotDatum d r hp hq`, chart family
`pivotAtlasFibreChart` (per-pivot `AtlasFibreChart` — bare-`k` trivialization + over-base product +
flatness), cover the `PivotDatum`-indexed scheme open-cover
`iUnion_pivotDatum_basicOpen_eq_rankROpen`. Every field is a
banked, machine-checked DLN fact, so the instance is axiom-clean — an inhabited instance witnessing
that the abstract predicate is satisfiable by the DLN bundle (nonemptiness of `rankROpen` is a
separate, unproved claim). The open `rankROpen` is load-bearing: a bundle over the closure `Σ̄^r` is
false (the rank-`< r` boundary lies in no chart). -/
noncomputable def reducedFibre_isZariskiLocallyTrivialAffineProduct (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Algebra.IsZariskiLocallyTrivialAffineProduct k (sweepSigmaRing k d r)
      (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq)
      (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (sweepFibreRing k d r hp hq)
      (rankROpen (k := k) d r) where
  ι := PivotDatum d r hp hq
  chart I := pivotAtlasFibreChart d r hp hq I
  cover := by
    -- `(chart I).chartElt = (pivotAtlasChart I).chartElt = pivotElt I = chartDsigAt I.s I.t`.
    simpa only [pivotAtlasFibreChart, pivotAtlasChart_chartElt, pivotElt]
      using iUnion_pivotDatum_basicOpen_eq_rankROpen (k := k) d r hp hq

/-! ## Inhabitation witnesses -/

section Witness

/-- **The derived cocycle fires on the DLN instance.** The atlas overlap transition round-trips to
the identity at every pair of pivots — a proven property of the predicate (P2.c), not a field. -/
example {k : Type} [Field k] [Infinite k] {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I J : PivotDatum d r hp hq) :
    letI A := reducedFibre_isZariskiLocallyTrivialAffineProduct (k := k) d r hp hq
    ((A.chart I).toAtlasChart.overlapTransition (A.chart J).toAtlasChart).trans
        ((A.chart J).toAtlasChart.overlapTransition (A.chart I).toAtlasChart)
      = AlgEquiv.refl (R := k) :=
  Algebra.IsZariskiLocallyTrivialAffineProduct.overlapTransition_trans_symm
    (reducedFibre_isZariskiLocallyTrivialAffineProduct (k := k) d r hp hq) I J

end Witness

end DLNFibre.Core
