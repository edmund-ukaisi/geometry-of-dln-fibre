/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreBundleLocallyTrivialFull
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# `DLNFibre.Core.FibreFlatness` — flatness facts around the DLN fibre atlas (S3)

Flatness facts attached to the per-pivot local-product atlas
(`reducedFibre_pivotLocalProductAtlasOnRankOpen`). **Read the scope honestly:** the brief's S3
target — the flat fibre-family projection `mult⁻¹(rankROpen) → rankROpen` — is **NOT delivered**
(blocker named below). What IS delivered are two genuinely-true flatness facts and the in-file
**cheap-flatness verdict** that settles which routes are cheap.

## The cheap-flatness verdict (the S3 kill-condition, settled in-file)

The "structure map of the bundle's coordinate ring over the base" reads two ways, and they have
**different** content — and *neither* needed miracle/generic flatness:

1. **The chart inclusion `Base → Total`** (`Base = sweepSigmaRing`, `Total = Away (chartDsigAt …)`)
   is a **localization**, hence flat **for free** — `IsLocalization.flat`, independent of the Schur
   charts, the trivialization, and the rank bridge. This is the *open-chart-inclusion* flatness
   (`D(chartDsigAt …) ↪ Spec Base`), **NOT** the fibre-family flatness over the base. Recorded as
   `chartInclusion_flat`. Cheap; not the payoff.
2. **The standard fibre model `SchurLoc ⊗_k sweepFibreRing` over the auxiliary ring `SchurLoc`** is
   **free**, hence flat (`Module.Free.tensor`: `SchurLoc` free over itself ⊗ `sweepFibreRing` free
   over the field `k`). ⚠ This is **generic base change**, true for *any* `k`-algebra in the right
   factor — the DLN geometry plays no role, and `SchurLoc` is the auxiliary *Schur coordinate ring
   inside each chart*, **not** the bundle base `rankROpen ⊆ Spec(Base)`. Recorded as
   `standardFibreModel_free` / `standardFibreModel_flat`. Cheap; **not** the fibre-family flatness
   over the base either (see the blocker).

## ⚠ THE S3 `Flat π` TARGET IS NOT MET HERE — the `SchurLoc`-linear rung now lands downstream (S4b)

The brief asks for `Flat π : mult⁻¹(rankROpen) → rankROpen` (the fibre family flat over the geometric
base). Delivering it through the atlas needs the chart trivialization to be **`SchurLoc`-linear** —
`Total ≃ₐ[SchurLoc] SchurLoc ⊗_k sweepFibreRing`. THIS module's `chartDsigAt_tensorEquiv` is only a
**`k`-algebra** equiv (`≃ₐ[k]`), so:

* `standardFibreModel_flat` does **NOT** transport here — `Localization.Away (chartDsigAt s t)` carries
  no `SchurLoc`-module structure compatible with the bare `k`-trivialization;
* so the facts in this module are over the *auxiliary* `SchurLoc` (generic base change), not a base.

The `SchurLoc`-linear trivialization rung **is now built downstream** in
`DLNFibre.Core.FibreOverBaseTriv` (`chartDsigAt_schurLocTensorEquiv` + `chartDsigAt_flat_over_schurLoc`),
giving chartwise flatness over the in-chart base direction `SchurLoc`. (`FibreFlatness` cannot
forward-import it — `FibreOverBaseTriv` imports this module.) That still does **not** close the `Flat π`
target: the remaining open items are (i) **projection compatibility** — that the in-chart structure map
`schurToDsigAt` is the pullback of `mult`'s projection from the target/base rank-chart — and (ii)
R1/global gluing. This module records the two cheap true facts + the cheap-flatness verdict, not the
payoff.

**Forward pointer (S4b, downstream).** The `SchurLoc`-linear upgrade IS delivered downstream in
`DLNFibre.Core.FibreOverBaseTriv` (`chartDsigAt_schurLocTensorEquiv` + `chartDsigAt_flat_over_schurLoc`),
giving chartwise fibre-family flatness **over the in-chart Schur ring `SchurLoc`**. (`FibreFlatness`
cannot forward-import it: `FibreOverBaseTriv` imports this module.) NB this is flatness over `SchurLoc`,
which is NOT yet literally `Flat π` over the geometric base. `SchurLoc` is the in-chart base DIRECTION;
`Away (chartDsigAt …)` is the source/total chart (a localization of `sweepSigmaRing`, already
`≅ SchurLoc ⊗ sweepFibreRing`). Reading this as fibre-family flatness over the genuine base needs
(i) **projection compatibility** — that `schurToDsigAt : SchurLoc → Away (chartDsigAt …)` is the pullback
of `mult`'s projection from the target/base rank-chart — and (ii) R1 (`targetOverlapTransition`) to glue
a single global morphism; both roadmapped, projection compatibility ahead of R1.

## Main results (what is actually proved)

* `chartInclusion_flat` — `Module.Flat Base (Away (chartDsigAt s t))` (localization; chart-inclusion
  side, NOT the fibre-family payoff).
* `standardFibreModel_free` / `standardFibreModel_flat` — `Module.Free`/`Module.Flat SchurLoc
  (SchurLoc ⊗_k sweepFibreRing)`: the standard model is free, hence flat, over the **auxiliary**
  `SchurLoc` (generic base change; NOT flatness of the fibre family over the base — see blocker).
* `flat_specMap_standardFibreModelOverSchur` — scheme-level `AlgebraicGeometry.Flat (Spec.map …)` of
  the algebraMap-induced map `Spec(SchurLoc ⊗ sweepFibreRing) → Spec(SchurLoc)` (the model over the
  auxiliary `SchurLoc`, not over the bundle base).
* `universallyOpen_specMap_standardFibreModelOverSchur` — corollary `UniversallyOpen` (`Flat` +
  `LocallyOfFinitePresentation` via `UniversallyOpen.of_flat`) of that same map.

**name = content honesty:** the names denote flatness of the **standard model over `SchurLoc`** and
of a **chart inclusion** — not "the bundle is flat over its base." The `rankAtStalk`-locally-const.
corollary is **NOT** included: it needs `Module.FinitePresentation SchurLoc (SchurLoc ⊗
sweepFibreRing)` as a *module* (a finite-rank vector bundle), which fails (the fibre has positive
dimension, so the family is not a finite module). See the gap note at the foot of the file.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Algebra MvPolynomial Matrix TensorProduct AlgebraicGeometry CategoryTheory

/-! ## (1) The cheap chart-inclusion flatness — a localization is flat over the base -/

section ChartInclusion

variable {k : Type} [Field k] {N : ℕ}

/-- **The chart inclusion is flat (the cheap-flatness verdict, chart-inclusion side).** The
structure map `Base → Total` of a single per-pivot chart — `sweepSigmaRing k d r → Localization.Away
(chartDsigAt s t)` — is **flat**, because it is a localization (`Localization.flat`). This is
automatic: it needs neither the Schur trivialization, nor the rank bridge, nor generic/miracle
flatness. It is the *open-chart-inclusion* flatness (`D(chartDsigAt s t) ↪ Spec Base`), **not** the
bundle/fibre-family flatness payoff (that is `standardFibreModel_flat`). -/
theorem chartInclusion_flat (d : Fin (N + 2) → ℕ) (r : ℕ)
    (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0)) :
    Module.Flat (sweepSigmaRing k d r)
      (Localization.Away (chartDsigAt (k := k) d r s t)) :=
  Localization.flat _ (Submonoid.powers (chartDsigAt (k := k) d r s t))

end ChartInclusion

/-! ## (2) The standard fibre model is free, hence flat, over the auxiliary `SchurLoc`

⚠ This is **generic base change** (any `k`-algebra in the right factor), and `SchurLoc` is the
auxiliary Schur coordinate ring **inside each chart**, NOT the bundle base. It is **not** flatness
of the DLN fibre family over the base — that needs a `SchurLoc`-linear trivialization the atlas does
not yet provide (module blocker, see the header). -/

section StandardFibreModel

variable {k : Type} [Field k] {N : ℕ}

/-- **The standard fibre model is FREE over the auxiliary `SchurLoc`.** The standard fibre model
`SchurLoc ⊗_k sweepFibreRing` — the codomain every per-pivot trivialization maps to — is a **free**
`SchurLoc`-module: `SchurLoc` is free over itself, `sweepFibreRing` is free over the field `k`, so
their tensor over `k` is free over the left factor `SchurLoc` (`Module.Free.tensor`). ⚠ This is
**generic base change** for *any* `k`-algebra in the right factor (no DLN geometry is used), and
`SchurLoc` is the auxiliary Schur direction *inside the chart*, not the bundle base
`rankROpen ⊆ Spec(Base)`. So it is **not** the fibre-family flatness over the base (which needs a
`SchurLoc`-linear trivialization — see the module header's blocker). -/
theorem standardFibreModel_free (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Module.Free (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq) :=
  inferInstance

/-- **The standard fibre model is FLAT over the auxiliary `SchurLoc`.** Immediate from freeness
(`standardFibreModel_free` + `Module.Flat.of_free`). ⚠ As with `standardFibreModel_free`, this is
generic base change over the *auxiliary* `SchurLoc` (the in-chart Schur direction), **not** flatness
of the DLN fibre family over the bundle base: the atlas trivialization is only `k`-linear, so this
does NOT transport to the chart total ring `Localization.Away (chartDsigAt s t)` over the base. The
fibre-family flatness (brief S3) is open pending the `SchurLoc`-linear trivialization. -/
theorem standardFibreModel_flat (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq) :=
  Module.Flat.of_free

end StandardFibreModel

/-! ## (3) The scheme-level flatness + the `UniversallyOpen` corollary -/

section Scheme

variable {k : Type} [Field k] {N : ℕ}

/-- **The standard model is flat over the auxiliary `SchurLoc` at the scheme level.** The morphism
of affine schemes `Spec (SchurLoc ⊗_k sweepFibreRing) → Spec SchurLoc` induced by the algebraMap is
`AlgebraicGeometry.Flat`: the ring map is flat (`standardFibreModel_flat` via
`RingHom.flat_algebraMap_iff`), and flatness of `Spec.map` is the ring-hom property
(`HasRingHomProperty.Spec_iff (P := @Flat)`). ⚠ This is the model over the *auxiliary* `SchurLoc`,
**not** the fibre family over the bundle base (see the module header's blocker). -/
theorem flat_specMap_standardFibreModelOverSchur (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom
      (algebraMap (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
        (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
  rw [CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
  exact standardFibreModel_flat d r hp hq

/-- **The standard-model-over-`SchurLoc` projection is universally open.** Combining scheme-level
flatness (`flat_specMap_standardFibreModelOverSchur`) with local finite presentation (the standard
model is finitely presented over `SchurLoc` — base change of the finitely-presented `k`-algebra
`sweepFibreRing`), `UniversallyOpen.of_flat` gives universal openness. ⚠ Of the map to the
*auxiliary* `SchurLoc`, not the bundle base (see the module header's blocker). -/
theorem universallyOpen_specMap_standardFibreModelOverSchur (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    AlgebraicGeometry.UniversallyOpen (Spec.map (CommRingCat.ofHom
      (algebraMap (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
        (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq)))) := by
  -- the scheme map is flat (model over the auxiliary `SchurLoc`) …
  haveI hflat := flat_specMap_standardFibreModelOverSchur (k := k) d r hp hq
  -- … and locally of finite presentation: the standard model is fp over `SchurLoc` (base change of
  -- the fp `k`-algebra `sweepFibreRing`), so `Spec.map (algebraMap …)` is locally of fin. pres.
  haveI hfpk : Algebra.FinitePresentation k (sweepFibreRing k d r hp hq) :=
    Algebra.FinitePresentation.quotient
      (IsNoetherian.noetherian (vanishingIdeal k (sweepFibre k d r hp hq)))
  haveI hfpbc : Algebra.FinitePresentation (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq) :=
    Algebra.FinitePresentation.baseChange (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
  haveI hfp : AlgebraicGeometry.LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
      (algebraMap (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
        (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.LocallyOfFinitePresentation),
      CommRingCat.hom_ofHom, RingHom.finitePresentation_algebraMap]
    exact hfpbc
  exact AlgebraicGeometry.UniversallyOpen.of_flat _

end Scheme

/-! ## The atlas connection — every chart trivializes (k-linearly) onto the SchurLoc-flat model

`standardFibreModel_flat` is stated on the standard fibre model `SchurLoc ⊗_k sweepFibreRing`. The
per-pivot atlas's trivialization `chartDsigAt_tensorEquiv` exhibits **each** chart total ring
`Localization.Away (chartDsigAt s t)` as this model — but only as a **`k`-algebra** equiv. ⚠ Because
the equiv is `k`-linear and not `SchurLoc`-linear, the model's `SchurLoc`-flatness does **NOT**
transport to the chart ring; this section records only the bare existence of the `k`-equiv alongside
the model flatness, the two as **separate** facts, NOT a flatness of the chart ring over a base. -/

section AtlasConnection

variable {k : Type} [Field k] [Infinite k] {N : ℕ}

/-- **Atlas connection witness (two separate facts, k-linear link only).** The atlas trivialization
`chartDsigAt_tensorEquiv` is a **`k`-algebra** equiv from the chart total ring
`Localization.Away (chartDsigAt s t)` onto the standard model `SchurLoc ⊗_k sweepFibreRing`, and the
model is flat over `SchurLoc` (`standardFibreModel_flat`). ⚠ These are recorded as a **conjunction
of two facts**, NOT a transport: the equiv is `k`-linear, so it does **not** carry the
`SchurLoc`-flatness to the chart ring. So this witness does **not** establish flatness of the chart
total ring over the base (or over `SchurLoc`); it only records that the chart ring is `k`-algebra
isomorphic to a ring that is `SchurLoc`-flat. The genuine bundle flatness needs the `SchurLoc`-lin.
trivialization (module header blocker). -/
theorem exists_chart_trivialization_onto_flat_model (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0))
    (σ : Equiv.Perm (Fin (d (Fin.last (N + 1))))) (τ : Equiv.Perm (Fin (d 0)))
    (hσ : ∀ i : Fin r, σ (Fin.castLE hp i) = s i)
    (hτ : ∀ j : Fin r, τ (Fin.castLE hq j) = t j) :
    Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
        (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq) ∧
      Nonempty (Localization.Away (chartDsigAt (k := k) d r s t)
        ≃ₐ[k] SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq) :=
  ⟨standardFibreModel_flat d r hp hq, ⟨chartDsigAt_tensorEquiv d r hp hq s t σ τ hσ hτ⟩⟩

end AtlasConnection

/-! ## Recorded gaps (honesty)

* **⚠ THE S3 `Flat π` TARGET — flatness of the fibre family over the geometric base — is NOT delivered
  in THIS module.** The brief's S3 is `Flat π : mult⁻¹(rankROpen) → rankROpen`. This module's
  `chartDsigAt_tensorEquiv` is only `k`-linear (`≃ₐ[k]`), so `standardFibreModel_flat` (flatness over
  the *auxiliary* `SchurLoc`, generic base change) does NOT transport here. The `SchurLoc`-linear
  trivialization rung is built **downstream** (`FibreOverBaseTriv`: `chartDsigAt_schurLocTensorEquiv` /
  `chartDsigAt_flat_over_schurLoc`), giving chartwise flatness over `SchurLoc`; the `Flat π` target then
  remains open on (i) **projection compatibility** (the in-chart structure map = `mult`'s projection
  pullback) and (ii) R1/global gluing — see those modules. This module delivers the cheap-flatness
  verdict + two true side-facts, not the payoff.
* **Global (single-morphism) flatness over all of `rankROpen`.** Even granting a per-chart
  fibre-family flatness, a single *global* `AlgebraicGeometry.Flat` for one morphism over the whole
  `rankROpen ⊆ Spec(sweepSigmaRing)` would additionally need the target-overlap gluing data
  (`targetOverlapTransition`, roadmap R1) to assemble the per-chart trivializations into one bundle
  morphism. (Secondary to the primary blocker above.)
* **`rankAtStalk` locally constant is NOT included.** `Module.isLocallyConstant_rankAtStalk` needs
  `Module.FinitePresentation SchurLoc (SchurLoc ⊗ sweepFibreRing)` as a *module* (a vector bundle of
  finite rank). The DLN fibre has positive dimension, so the family is **not** a finite module — the
  corollary genuinely does not apply (it is a vector-bundle statement, and this is a non-finite
  fibre family). `UniversallyOpen` is the corollary that does apply and is delivered.
-/

end DLNFibre.Core
