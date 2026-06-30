/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.RingTheory.Spectrum.Prime.Topology
import DLNFibre.Core.RingTheory.Determinantal.AtlasTransition

/-!
# `Algebra` — Zariski local-triviality of an affine product over an open

The capstone predicate of the constructive pivot-chart atlas: a base ring `Base`, an open set
`U ⊆ Spec Base`, and a family of charts that **Zariski-locally trivialize an affine product over
`U`**. Over a base field `k`, this names exactly "locally a product over a principal-open cover of
`U`": a family of `Algebra.AtlasFibreChart`s — each a principal open `D(chartElt)` of `Base` paired
with an over-base trivialization of the localized chart total ring as the fixed standard fibre model
`BaseLoc ⊗_k Fibre` — whose charts cover `U`.

There is no algebraic / Zariski local-triviality class in Mathlib v4.29: its only `FiberBundle` is
**topological** (it needs `[TopologicalSpace B]` and local *homeomorphic* trivializations). This is
the bespoke Zariski analogue, network-free over arbitrary `k`-algebras.

## The two genuine data, and why no cocycle field

A Zariski-locally-trivial affine product over an open `U` carries exactly:

1. a **principal-open cover** of `U` by the charts `D((chart i).chartElt)`;
2. a **per-chart over-base product trivialization** — `Algebra.AtlasFibreChart` already bundles one
   chart's data: the base element `chartElt` (for the cover) + the bare-`k` trivialization
   `trivK : Away chartElt ≃ₐ[k] M` (for the transitions) + the over-base `fibreModel :
   StandardFibreChart` (the `≃ₐ[BaseLoc]` local product + flatness).

The transition/cocycle compatibility is **NOT** a field. The pairwise round-trip
`overlapTransition C D ≪≫ overlapTransition D C = refl` is a THEOREM that holds for ANY two
`AtlasChart`s (`Algebra.AtlasChart.overlapTransition_trans_symm`, P2.c) — it is automatically
satisfied, never a constraint to discharge. Adding it as a field the instance must fill by hand
would be busy-work and would misrepresent the content. Instead the "atlas glues compatibly" content
is recorded as a **derived lemma** about any such atlas — `overlapTransition_trans_symm` /
`overlapTransition_symm` below — a PROVEN property of the predicate, not a field. So the predicate's
content is faithfully "locally a product over a principal-open cover of `U`", with the cocycle as a
free consequence.

## `name = content`: the open `U` is load-bearing

The predicate names local-triviality over the **open** `U`. For the DLN instance `U` is the rank-`=
r` open; a bundle over the closure `Σ̄^r = Spec(sweepSigmaRing)` is **FALSE** (the rank-`< r`
boundary lies in no chart). So `U` is part of the statement, not decoration: the cover hypothesis
`(⋃ i, D((chart i).chartElt)) = U` is over `U`, never over all of `Spec Base`.

## What is built

* `Algebra.IsZariskiLocallyTrivialAffineProduct k Base M BaseLoc Fibre U` — the **predicate**: a
  family `chart : ι → AtlasFibreChart` (`ι` a field of the structure) + the cover hypothesis
  `cover : (⋃ i, D((chart i).chartElt)) = U`.
* `Algebra.IsZariskiLocallyTrivialAffineProduct.overlapTransition_trans_symm` /
  `…overlapTransition_symm` — the **derived** cocycle compatibility of the atlas (from P2.c), a
  proven property, not a field.

The eventual Mathlib home is the algebraic-geometry / localization-atlas library, so the predicate
lives in the bare `Algebra` namespace (L7 Mathlib-mirror), network-free over arbitrary `k`-algebras.

**Dependency rule:** network-free `Core` — never import `DLNFibre.DLN`.
-/

open scoped TensorProduct

namespace Algebra

universe u

/-! ## The predicate: Zariski-locally-trivial affine product over an open -/

/-- **A Zariski-locally-trivial affine product over an open `U ⊆ Spec Base`.** Over a base field
`k`, with a fixed standard fibre model `M` and its base direction / fibre split `BaseLoc`, `Fibre`,
this bundles the genuine content of "locally a product over a principal-open cover of `U`":

* an index type `ι` and a chart family `chart : ι → AtlasFibreChart k Base M BaseLoc Fibre` — each
  chart a principal open `D((chart i).chartElt)` of `Base` paired with the bare-`k` trivialization
  `trivK : Away chartElt ≃ₐ[k] M` AND the over-base fibre model `fibreModel : StandardFibreChart`
  (the `≃ₐ[BaseLoc] BaseLoc ⊗_k Fibre` local product + `BaseLoc`-flatness);
* `cover` — the principal-open charts cover `U`: `(⋃ i, (D((chart i).chartElt) : Set _)) = U`.

The transition/cocycle compatibility is intentionally NOT a field — it holds automatically for any
two `AtlasChart`s (P2.c `Algebra.AtlasChart.overlapTransition_trans_symm`) and is recorded as the
DERIVED lemma `IsZariskiLocallyTrivialAffineProduct.overlapTransition_trans_symm`. The open `U` is
load-bearing: a bundle over the closure is generically false (the boundary lies in no chart). -/
structure IsZariskiLocallyTrivialAffineProduct
    (k : Type u) [CommRing k]
    (Base : Type u) [CommRing Base] [Algebra k Base]
    (M : Type u) [CommRing M] [Algebra k M]
    (BaseLoc : Type u) [CommRing BaseLoc] [Algebra k BaseLoc]
    (Fibre : Type u) [CommRing Fibre] [Algebra k Fibre]
    (U : Set (PrimeSpectrum Base)) where
  /-- The chart index type. -/
  ι : Type u
  /-- The chart family: at each index, an `AtlasFibreChart` (principal open `D(chartElt)` + bare-`k`
  trivialization `trivK` + the over-base fibre model `fibreModel`). -/
  chart : ι → AtlasFibreChart k Base M BaseLoc Fibre
  /-- The principal-open charts `D((chart i).chartElt)` cover the open `U`. -/
  cover :
    (⋃ i : ι, (PrimeSpectrum.basicOpen (chart i).chartElt : Set (PrimeSpectrum Base))) = U

namespace IsZariskiLocallyTrivialAffineProduct

variable {k : Type u} [CommRing k]
  {Base : Type u} [CommRing Base] [Algebra k Base]
  {M : Type u} [CommRing M] [Algebra k M]
  {BaseLoc : Type u} [CommRing BaseLoc] [Algebra k BaseLoc]
  {Fibre : Type u} [CommRing Fibre] [Algebra k Fibre]
  {U : Set (PrimeSpectrum Base)}

/-! ## The derived cocycle compatibility (NOT a field — a proven property, P2.c) -/

/-- **The overlap transition of the atlas round-trips to the identity (derived cocycle, P2.c).** For
any two charts `i, j` of a Zariski-locally-trivial affine product, the pairwise round trip on the
target/model overlap presentations is the identity — this is `Algebra.AtlasChart.overlapTransition_
trans_symm` at `(chart i).toAtlasChart`, `(chart j).toAtlasChart`. It is a PROVEN property of the
predicate, not a field the instance must discharge: the cocycle is automatically satisfied for any
atlas of `AtlasChart`s. The cocycle lives on the bare-`k` `trivK`/`M` presentation
(`overlapTransition` conjugates through `trivK`), DECOUPLED from the over-`BaseLoc`
`fibreModel.triv` product — it is NOT an over-base-product cocycle. -/
theorem overlapTransition_trans_symm
    (A : IsZariskiLocallyTrivialAffineProduct k Base M BaseLoc Fibre U) (i j : A.ι) :
    ((A.chart i).toAtlasChart.overlapTransition (A.chart j).toAtlasChart).trans
        ((A.chart j).toAtlasChart.overlapTransition (A.chart i).toAtlasChart)
      = AlgEquiv.refl (R := k) :=
  AtlasChart.overlapTransition_trans_symm (A.chart i).toAtlasChart (A.chart j).toAtlasChart

/-- **The inverse of the atlas overlap transition is the swapped transition (derived, P2.c).**
`(overlapTransition i j).symm = overlapTransition j i` — the cocycle round-trip read as a
characterization of the inverse (`Algebra.AtlasChart.overlapTransition_symm` at the charts). -/
theorem overlapTransition_symm
    (A : IsZariskiLocallyTrivialAffineProduct k Base M BaseLoc Fibre U) (i j : A.ι) :
    ((A.chart i).toAtlasChart.overlapTransition (A.chart j).toAtlasChart).symm
      = (A.chart j).toAtlasChart.overlapTransition (A.chart i).toAtlasChart :=
  AtlasChart.overlapTransition_symm (A.chart i).toAtlasChart (A.chart j).toAtlasChart

/-! ## The two-worlds bridge view (AG-facing accessors)

The predicate names a **ring/algebra** object, but it sits at the junction of two naming worlds,
and the word "base" is overloaded between them because **`Spec` is contravariant**. This section
adds an additive scheme/AG-facing **view** — accessors that re-expose the SAME data under scheme
names, with NO change to the predicate. Both name-sets are correct, each in its own world.

### Ring-side ↔ scheme-side dictionary (ring name → scheme name; DLN meaning)

* `Base` (the algebra's base ring) → `totalSpace = Spec Base`, the ambient **total** affine space
  (DLN: `Σ̄^r`). Local triviality holds over the open `U ⊆ totalSpace`, not all of it.
* `BaseLoc` (the ring each chart is a product *over*) → `chartBaseSpace i = Spec BaseLoc`, the
  fibration **base** (DLN: the rank-chart `SchurLoc`).
* `Fibre` → `fibreSpace = Spec Fibre`, the **model fibre** factor (DLN: `sweepFibreRing`). The
  scheme-theoretic fibres over points of `Spec BaseLoc` are base changes of this model fibre.
* `(chart i).fibreModel.structMap : BaseLoc →ₐ[k] Total` → `chartProjection i`, the comorphism
  projection `Spec Total → Spec BaseLoc` on the chart domain (DLN: `π : D(chartElt) → SchurLoc`).

`Spec` contravariance is what flips top↔bottom: the structure map `structMap : BaseLoc → Total`
points base→total in the RING world, so its comorphism `comap structMap : Spec Total → Spec BaseLoc`
points total→base in the SCHEME world. Hence `Base` is the *total* ring while `Spec Base` is the
*total* space, and `BaseLoc` is the over-ring while `Spec BaseLoc` is the fibration *base* — both
names are correct, each in its own world.

### Honest boundary (name = content): the projection is PER-CHART only

`chartProjection` is exposed **per chart** `i`: its domain is `Spec(Away (chart i).chartElt)`, the
localized affine spectrum canonically corresponding to the chart's own basic open
`D((chart i).chartElt)` — NOT all of `U`. A SINGLE GLOBAL fibration morphism `π : U → (base)` over
all of `U` is NOT constructed here: it needs an actual gluing of the per-chart projections from
their overlap-compatibility data (roadmap R1 / the P2.c′ target-side gluing), which this view does
not build or prove. The view does NOT assert a global projection: it exposes exactly the chartwise
picture the predicate proves (chartwise local triviality + the 2-fold overlap cocycle of
`overlapTransition_trans_symm`). This is a renaming view — it adds no new data and no new
theorems. -/

section FibrationView

/-- AG-facing ambient **total space** `Spec Base` (DLN: `Σ̄^r`); local triviality holds over `U`. -/
def totalSpace
    (_A : IsZariskiLocallyTrivialAffineProduct k Base M BaseLoc Fibre U) :
    Type u := PrimeSpectrum Base

/-- AG-facing **model fibre** factor `Spec Fibre` (DLN: `Spec(sweepFibreRing)`). -/
def fibreSpace
    (_A : IsZariskiLocallyTrivialAffineProduct k Base M BaseLoc Fibre U) :
    Type u := PrimeSpectrum Fibre

/-- AG-facing **per-chart fibration base** `Spec BaseLoc` (DLN: the rank-chart `SchurLoc`). -/
def chartBaseSpace
    (_A : IsZariskiLocallyTrivialAffineProduct k Base M BaseLoc Fibre U) (_i : _A.ι) :
    Type u := PrimeSpectrum BaseLoc

/-- AG-facing **per-chart** fibration projection `Spec(Away chartElt) → Spec BaseLoc`, the
comorphism `comap (fibreModel.structMap)` on the chart domain `D(chartElt)`; per-chart, NOT a
global `π` on `U`. -/
def chartProjection
    (A : IsZariskiLocallyTrivialAffineProduct k Base M BaseLoc Fibre U) (i : A.ι) :
    PrimeSpectrum (Localization.Away (A.chart i).chartElt) → PrimeSpectrum BaseLoc :=
  PrimeSpectrum.comap (A.chart i).fibreModel.structMap.toRingHom

end FibrationView

end IsZariskiLocallyTrivialAffineProduct

end Algebra
