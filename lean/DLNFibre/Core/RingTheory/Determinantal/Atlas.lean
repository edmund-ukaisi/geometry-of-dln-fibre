/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic

/-!
# `Algebra` — the standard fibre model of an affine atlas chart

The **standard fibre model** of one chart of a Zariski-locally-trivial affine product: over a base
field `k`, a `k`-algebra trivialization of a chart's localized total coordinate ring as a tensor
product `BaseLoc ⊗_k Fibre` of the in-chart base direction with the fibre, **respecting the base** —
an honest `BaseLoc`-algebra iso, not a bare `k`-algebra iso — together with the flatness of the
total ring over the base direction. This is the per-chart datum of a constructive pivot-chart atlas,
stated abstractly over arbitrary `k`-algebras so it is network-free and reusable.

## The two data this packages, and why one structure

A single chart of a locally trivial affine fibre family carries, beyond the bare `k`-algebra product
`Total ≃ₐ[k] BaseLoc ⊗_k Fibre`, the **over-base** content: the total ring is a `BaseLoc`-algebra
via an *honest* structure map `structMap : BaseLoc →ₐ[k] Total` (presenting `Spec BaseLoc` as the
in-chart base), and the trivialization respects that structure (a `≃ₐ[BaseLoc]`, not merely a
`≃ₐ[k]`), and the total ring is `BaseLoc`-flat. The over-base iso only typechecks once `Total` is a
`BaseLoc`-algebra, so the structure map must be a *field* of the datum, with the `triv`/`flat` read
over the `structMap`-induced algebra (the `letI := structMap.toRingHom.toAlgebra` pattern). Bundling
the structure map into the datum is exactly what lets a consumer drop the per-chart threading of the
maps that build it.

## What is built

* `Algebra.StandardFibreChart k Total BaseLoc Fibre` — the **over-base standard fibre model datum**:
  the chart base element `chartElt` is omitted (it lives with the cover, not the fibre model); the
  datum carries `structMap`, the over-base trivialization `triv`, and the flatness `flat`. It is the
  network-free generalization of the DLN bundle layer's per-pivot `OverBaseChartDatum`.
* `Algebra.StandardFibreChart.flatModel` — the model side `BaseLoc ⊗_k Fibre` is itself
  `BaseLoc`-flat when `Fibre` is `k`-flat (base change), recorded so the datum's `flat` field is a
  genuine *transport* across `triv`, not an independent assumption.
* `Algebra.StandardFibreChart.ofTrivialization` — **the constructor**: from a structure map and an
  over-base trivialization alone, the flatness comes for free (transport `flatModel` across `triv`).
  So a consumer supplies the two genuinely-geometric data; the flatness is derived.

The eventual Mathlib home is the algebra-tensor / flatness library, so the datum lives in the bare
`Algebra` namespace (L7 Mathlib-mirror), network-free over arbitrary `k`-algebras.

**Dependency rule:** network-free `Core` — never import `DLNFibre.DLN`.
-/

open scoped TensorProduct

namespace Algebra

universe u

variable (k : Type u) [CommRing k]

/-! ## The over-base standard fibre model datum -/

/-- **The standard fibre model of one atlas chart (over-base).** For a base ring `k`, this bundles
the per-chart fibre-model data of a Zariski-locally-trivial affine product: a localized chart total
ring `Total`, the in-chart base direction `BaseLoc`, the fibre coordinate ring `Fibre`, and

* `structMap : BaseLoc →ₐ[k] Total` — the HONEST structure map exhibiting `Total` as a
  `BaseLoc`-algebra (presenting `Spec BaseLoc` as the in-chart base direction), carried as a field
  so the over-base data below typecheck without threading the maps that build it;
* `triv` — the OVER-BASE trivialization: with the `structMap`-induced `BaseLoc`-algebra structure on
  `Total`, a `BaseLoc`-algebra iso `Total ≃ₐ[BaseLoc] BaseLoc ⊗_k Fibre` (the local product,
  respecting the base — not merely a bare `≃ₐ[k]`);
* `flat` — FLATNESS over the base: with the same structure, `Total` is `BaseLoc`-flat.

This is the network-free generalization of the DLN bundle layer's per-pivot `OverBaseChartDatum`
(`DLNFibre.Core.FibreBundleHeadline`): there `Total = Away (chartDsigAt s t)`, `BaseLoc = SchurLoc`,
`Fibre = sweepFibreRing`, and `structMap = schurToDsigAt` (gauge ∘ deep-chart ∘ connecting), with
`s, t, σ, τ` threaded through every field; here all of that collapses into the three abstract rings
plus the one structure map. The chart base element (the principal open cut from the global base) is
intentionally NOT a field of this datum — it belongs with the cover, not the fibre model. -/
structure StandardFibreChart
    (Total : Type u) [CommRing Total] [Algebra k Total]
    (BaseLoc : Type u) [CommRing BaseLoc] [Algebra k BaseLoc]
    (Fibre : Type u) [CommRing Fibre] [Algebra k Fibre] where
  /-- The HONEST structure map `BaseLoc →ₐ[k] Total` exhibiting the chart total ring as a
  `BaseLoc`-algebra — the in-chart base direction presented inside the total ring. -/
  structMap : BaseLoc →ₐ[k] Total
  /-- The OVER-BASE trivialization: with the `structMap`-induced `BaseLoc`-algebra structure on
  `Total`, a `BaseLoc`-algebra iso `Total ≃ₐ[BaseLoc] BaseLoc ⊗_k Fibre`. -/
  triv :
    letI := structMap.toRingHom.toAlgebra
    Total ≃ₐ[BaseLoc] BaseLoc ⊗[k] Fibre
  /-- FLATNESS over the base: with the `structMap`-induced structure, `Total` is `BaseLoc`-flat. -/
  flat :
    letI := structMap.toRingHom.toAlgebra
    Module.Flat BaseLoc Total

namespace StandardFibreChart

variable {k}
variable {Total : Type u} [CommRing Total] [Algebra k Total]
  {BaseLoc : Type u} [CommRing BaseLoc] [Algebra k BaseLoc]
  {Fibre : Type u} [CommRing Fibre] [Algebra k Fibre]

/-! ## The model side is flat over the base direction (generic base change) -/

/-- **The standard fibre model is FLAT over its base direction.** When the fibre `Fibre` is
`k`-flat, the model `BaseLoc ⊗_k Fibre` is flat over the left factor `BaseLoc` by base change
(`Module.Flat.baseChange`: a flat module stays flat after extending scalars along `k → BaseLoc`).
This is **generic base change** — it uses no atlas geometry, only `k`-flatness of the fibre — and is
the reason the datum's `flat` field is a genuine transport across `triv`, not a fresh assumption. In
the typical case `Fibre` is `k`-free (e.g. a polynomial coordinate ring), hence `k`-flat. -/
theorem flatModel [Module.Flat k Fibre] : Module.Flat BaseLoc (BaseLoc ⊗[k] Fibre) :=
  inferInstance

/-! ## The constructor: flatness is derived from the over-base trivialization -/

/-- **Constructor — flatness for free from the over-base trivialization.** Given the two genuinely
geometric data of one chart — the honest structure map `structMap : BaseLoc →ₐ[k] Total` and the
over-base trivialization `e : Total ≃ₐ[BaseLoc] BaseLoc ⊗_k Fibre` (over the `structMap`-induced
algebra) — the `BaseLoc`-flatness of `Total` is automatic: transport the model's flatness
(`flatModel`) across `e` by `Module.Flat.of_linearEquiv`. So a consumer need only exhibit the
structure map and the over-base iso; the flatness field is filled here. -/
noncomputable def ofTrivialization [Module.Flat k Fibre] (structMap : BaseLoc →ₐ[k] Total)
    (e : letI := structMap.toRingHom.toAlgebra; Total ≃ₐ[BaseLoc] BaseLoc ⊗[k] Fibre) :
    StandardFibreChart k Total BaseLoc Fibre where
  structMap := structMap
  triv := e
  flat :=
    letI := structMap.toRingHom.toAlgebra
    haveI : Module.Flat BaseLoc (BaseLoc ⊗[k] Fibre) := flatModel
    Module.Flat.of_linearEquiv e.toLinearEquiv

end StandardFibreChart

/-! ## Non-vacuity

The genuine non-vacuous instance of `StandardFibreChart` is the DLN reduced-fibre bundle chart
`DLNFibre.Core.standardFibreChartOfPivot` (`DLNFibre.Core.FibreBundleHeadline`): at every pivot of
the determinantal atlas it builds a `StandardFibreChart` with `Total = Away (chartDsigAt s t)`,
`BaseLoc = SchurLoc`, `Fibre = sweepFibreRing`, structure map `schurToDsigAt`, over-base iso
`chartDsigAt_schurLocTensorEquiv`, and flatness `chartDsigAt_flat_over_schurLoc` — every field a
banked, machine-checked S4b fact. That is the geometric witness this abstract datum was extracted
from. -/

end Algebra
