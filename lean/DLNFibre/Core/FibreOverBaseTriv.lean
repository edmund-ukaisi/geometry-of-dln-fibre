/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreFlatness
import DLNFibre.Core.ChartEvalGauge
import DLNFibre.Core.ChartRoundTrip
import Mathlib.RingTheory.Flat.Basic

/-!
# `DLNFibre.Core.FibreOverBaseTriv` — the `SchurLoc`-linear (over-base) trivialization (S4b)

This module upgrades the per-pivot chart trivialization from a **`k`-algebra** equiv to a
**`SchurLoc`-algebra** equiv (over the in-chart Schur/base coordinate ring), and reads off chartwise
flatness over that in-chart base direction `SchurLoc`. (The S3 `Flat π` payoff — flatness over the
*geometric* base — additionally needs projection compatibility; see Scope.)

## The rung that was missing (S3/S4 convergent keystone)

The banked per-pivot trivialization `chartDsigAt_tensorEquiv`
(`Localization.Away (chartDsigAt s t) ≃ₐ[k] SchurLoc ⊗_k sweepFibreRing`) is only a **`k`-algebra**
equiv. We make it **`SchurLoc`-linear**:

> `Localization.Away (chartDsigAt s t) ≃ₐ[SchurLoc] SchurLoc ⊗_k sweepFibreRing`,

where `SchurLoc` acts on the chart total ring via an HONEST structure map (the composite of the
connecting map `schurToGfib`, the deep chart `chartLocalizedAlgEquiv.symm`, and the gauge transport
`awayCongr (gaugeEquivSigma …)`) — **not** by pulling back along the equiv we are upgrading.

## The crux

The whole upgrade collapses, after the gauge `awayCongr` legs cancel and the deep chart cancels, to
the SINGLE base-change identity (`reducedFibre_chartGfib_tensorEquiv_schurToGfib`): the keystone
tensor base-change `reducedFibre_chartGfib_tensorEquiv_reducedVariety` sends the connecting map
`schurToGfib x` to the left tensor factor `x ⊗ₜ 1`. This is `Localization.algHom_ext` reduced to the
generator lemma `mvPolynomialAwayMapTensorAlgEquiv_algebraMap_X` (the base-change keystone on `X v`,
established in `FibreBundleReduced` where the local product algebra instance lives) + the polynomial
base-change `algebraTensorAlgEquiv_symm_map`.

## Main results

* `reducedFibre_chartGfib_tensorEquiv_schurToGfib` — the crux: the keystone is `SchurLoc`-linear
  (`schurToGfib ↦ left tensor factor`).
* `reducedFibre_chartDsig_tensorEquiv_schurToDsig` / `chartDsigAt_tensorEquiv_schurToDsigAt` — the
  top-left / per-pivot `SchurLoc`-linearities (the banked `k`-trivializations send the honest
  structure map to the left tensor factor).
* `chartDsig_schurLocTensorEquiv` / `chartDsigAt_schurLocTensorEquiv` — the top-left / per-pivot
  **`SchurLoc`-algebra** trivializations `Away (chartDsig[At]) ≃ₐ[SchurLoc] SchurLoc ⊗_k
  sweepFibreRing` (the over-base local triviality; the per-pivot one over the `letI` structure-map
  algebra `chartDsigAtSchurLocAlgebra`, as the gauge `(σ, τ)` is not determined by the type).
* `chartDsig_flat_over_schurLoc` / `chartDsigAt_flat_over_schurLoc` — the top-left / per-pivot
  **flatness over the in-chart base direction `SchurLoc`** `Module.Flat SchurLoc (Away (chartDsig[At]))`,
  by `standardFibreModel_flat` across the `SchurLoc`-linear trivialization (chartwise; the S3 `Flat π`
  payoff additionally needs projection compatibility — see Scope).

## Scope (honest)

This is the CHARTWISE over-base trivialization + flatness, at every pivot, over the **named**
`SchurLoc`-algebra structure (`schurToDsigAt`). Two things stay open before this reads as flatness of
the geometric fibre-family projection:
(i) **projection compatibility** — that `schurToDsigAt : SchurLoc → Total` is the pullback of `mult`'s
projection from the target/base rank-chart. Until then `chartDsigAt_flat_over_schurLoc` is flatness over
the named `SchurLoc` algebra, NOT yet verified flatness of the geometric `mult`-projection, even
chartwise. (`Spec(sweepSigmaRing)` is the source/total; `SchurLoc` is only the base direction.)
(ii) R1 (`targetOverlapTransition`) — the overlap-gluing cocycle for a single GLOBAL `Flat π` /
`FiberBundle` morphism over all of `rankROpen`.
Both roadmapped (projection compatibility ahead of R1); NOT claimed here.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix TensorProduct

variable {k : Type} [Field k] {N : ℕ}

/-! ## The crux: the keystone tensor base-change is `SchurLoc`-linear -/

section Crux

/-- **The crux base-change identity.** The keystone tensor base-change
`reducedFibre_chartGfib_tensorEquiv_reducedVariety` sends the connecting algebra map
`schurToGfib x : Away chartGfib` to the left tensor factor `x ⊗ₜ 1`. This is the single genuinely
new compatibility behind the `SchurLoc`-linear upgrade: it says the tensor trivialization respects
the `SchurLoc`-action (`schurToGfib` on the source, left factor on the product). -/
theorem reducedFibre_chartGfib_tensorEquiv_schurToGfib (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (x : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) :
    reducedFibre_chartGfib_tensorEquiv_reducedVariety (k := k) d r hp hq (schurToGfib k d r hp hq x)
      = x ⊗ₜ[k] (1 : sweepFibreRing k d r hp hq) := by
  -- compare the two `k`-AlgHoms `SchurLoc →ₐ[k] SchurLoc ⊗ F` on `x`:
  --   `(tensorEquiv).toAlgHom.comp schurToGfib`  vs  `includeLeft`.
  have key : (reducedFibre_chartGfib_tensorEquiv_reducedVariety (k := k) d r hp hq).toAlgHom.comp
        (schurToGfib k d r hp hq)
      = (Algebra.TensorProduct.includeLeft :
          SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →ₐ[k]
            SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq) := by
    -- reduce to `MvPolynomial SchurVar k`-classes via `Localization.algHom_ext`.
    apply Localization.algHom_ext (Submonoid.powers (detSchurS (d 0) (d (Fin.last (N + 1))) r))
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply]
    change reducedFibre_chartGfib_tensorEquiv_reducedVariety (k := k) d r hp hq
        (schurToGfib k d r hp hq
          (algebraMap _ (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (X v)))
      = (Algebra.TensorProduct.includeLeft :
          SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →ₐ[k]
            SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq)
          (algebraMap _ (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (X v))
    -- LHS: push `schurToGfib` through the structure map, then the base-change keystone.
    rw [schurToGfib_algebraMap, Algebra.TensorProduct.includeLeft_apply]
    -- `mapAlgHom (ofId) (X v) = map (algebraMap k F) (X v)`, `chartGfib = map (…) detSchurS`,
    -- and the tensor equiv unfolds to `mvPolynomialAwayMapTensorAlgEquiv detSchurS`.
    rw [show (MvPolynomial.mapAlgHom (Algebra.ofId k (sweepFibreRing k d r hp hq))) (X v)
        = MvPolynomial.map (algebraMap k (sweepFibreRing k d r hp hq)) (X v) from rfl]
    exact mvPolynomialAwayMapTensorAlgEquiv_algebraMap_X
      (detSchurS (d 0) (d (Fin.last (N + 1))) r) v
  have := AlgHom.congr_fun key x
  simpa only [AlgHom.comp_apply, AlgHom.coe_coe, Algebra.TensorProduct.includeLeft_apply] using this

end Crux

/-! ## The top-left chart total ring as a `SchurLoc`-algebra + its `SchurLoc`-linear trivialization

The banked connecting map `schurToDsig : SchurLoc →ₐ[k] Away chartDsig`
(`chartPhiLoc ∘ schurToGfib`, the deep-chart pullback of `schurToGfib`) makes the top-left chart
total ring a `SchurLoc`-algebra, and the banked tensor trivialization is then `SchurLoc`-linear. -/

section TopLeft

variable [Infinite k]

/-- The deep chart `chartLocalizedAlgEquiv` carries the banked structure map `schurToDsig x` back to
the connecting map `schurToGfib x` (round-trip through `chartLocalizedAlgEquiv = ofAlgHom
chartPsiLoc chartPhiLoc`, with `schurToDsig = chartPhiLoc ∘ schurToGfib`). -/
theorem chartLocalizedAlgEquiv_schurToDsig (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (x : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) :
    chartLocalizedAlgEquiv k d r hp hq (schurToDsig k d r hp hq x) = schurToGfib k d r hp hq x := by
  rw [← chartPhiLoc_comp_schurToGfib, AlgHom.comp_apply]
  -- `chartPhiLoc = chartLocalizedAlgEquiv.symm`, so `chartLocalizedAlgEquiv (chartPhiLoc y) = y`.
  rw [show chartPhiLoc k d r hp hq (schurToGfib k d r hp hq x)
      = (chartLocalizedAlgEquiv (k := k) d r hp hq).symm (schurToGfib k d r hp hq x) from rfl,
    AlgEquiv.apply_symm_apply]

/-- **The top-left `SchurLoc`-linearity.** The top-left tensor trivialization
`reducedFibre_chartDsig_tensorEquiv_reducedVariety` sends the banked structure map `schurToDsig x`
to the left tensor factor `x ⊗ₜ 1`. Reduced to the crux
(`reducedFibre_chartGfib_tensorEquiv_schurToGfib`) via the deep-chart round-trip
(`chartLocalizedAlgEquiv_schurToDsig`). -/
theorem reducedFibre_chartDsig_tensorEquiv_schurToDsig (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (x : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) :
    reducedFibre_chartDsig_tensorEquiv_reducedVariety (k := k) d r hp hq
        (schurToDsig k d r hp hq x)
      = x ⊗ₜ[k] (1 : sweepFibreRing k d r hp hq) := by
  rw [reducedFibre_chartDsig_tensorEquiv_reducedVariety, AlgEquiv.trans_apply,
    chartLocalizedAlgEquiv_schurToDsig]
  exact reducedFibre_chartGfib_tensorEquiv_schurToGfib d r hp hq x

end TopLeft

/-! ## The per-pivot structure map + `SchurLoc`-linearity (before any local algebra instance)

These per-pivot structure-map definitions use `awayCongr`/`gaugeEquivSigma` over the base ring
`sweepSigmaRing`; they are placed before the trailing `local instance`s so instance search for those
gauge constructions is unaffected by the non-canonical `SchurLoc`-algebra structures we later put on
the chart total rings. -/

section PerPivotStruct

variable [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
  (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
  (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0))
  (σ : Equiv.Perm (Fin (d (Fin.last (N + 1))))) (τ : Equiv.Perm (Fin (d 0)))
  (hσ : ∀ i : Fin r, σ (Fin.castLE hp i) = s i) (hτ : ∀ j : Fin r, τ (Fin.castLE hq j) = t j)

/-- **The per-pivot chart structure map** `SchurLoc →ₐ[k] Away (chartDsigAt s t)`: the top-left
`schurToDsig` carried along the gauge transport `awayCongr (gaugeEquivSigma (pivotGauge σ τ))`
(taking `Away chartDsig` to `Away (chartDsigAt s t)`). An HONEST structure map (gauge ∘ deep-chart ∘
connecting map) exhibiting each chart total ring as a `SchurLoc`-algebra. -/
noncomputable def schurToDsigAt :
    SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →ₐ[k]
      Localization.Away (chartDsigAt (k := k) d r s t) :=
  (awayCongr (gaugeEquivSigma d r (pivotGauge d σ τ)) (chartDsig k d r hp hq)
      (chartDsigAt d r s t) (gaugeEquivSigma_chartDsig d r hp hq s t σ τ hσ hτ)).toAlgHom.comp
    (schurToDsig k d r hp hq)

/-- **The per-pivot `SchurLoc`-linearity.** The banked per-pivot tensor trivialization
`chartDsigAt_tensorEquiv` sends the structure map `schurToDsigAt x` to the left tensor factor
`x ⊗ₜ 1`. Reduced to the top-left `reducedFibre_chartDsig_tensorEquiv_schurToDsig` by the gauge
`awayCongr` round-trip (`chartDsigAt_tensorEquiv` = `(awayCongr gauge).symm` then chartDsig-tEq). -/
theorem chartDsigAt_tensorEquiv_schurToDsigAt
    (x : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) :
    chartDsigAt_tensorEquiv (k := k) d r hp hq s t σ τ hσ hτ
        (schurToDsigAt d r hp hq s t σ τ hσ hτ x)
      = x ⊗ₜ[k] (1 : sweepFibreRing k d r hp hq) := by
  rw [chartDsigAt_tensorEquiv, schurToDsigAt, AlgEquiv.trans_apply, AlgHom.comp_apply,
    AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.symm_apply_apply]
  exact reducedFibre_chartDsig_tensorEquiv_schurToDsig d r hp hq x

end PerPivotStruct

/-! ## The `SchurLoc`-algebra on the top-left chart total ring + its flatness over the base

We register the banked `schurToDsig` as the `SchurLoc`-algebra structure on `Away chartDsig` (a
`local instance`, confined to this module), promote the top-left trivialization to a
**`SchurLoc`-algebra** equiv, and read off chartwise flatness over the in-chart base direction
`SchurLoc` (the S3 `Flat π` payoff additionally needs projection compatibility). -/

section TopLeftFlat

variable [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
  (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)

/-- **The top-left chart total ring as a `SchurLoc`-algebra** (via the banked structure map
`schurToDsig`). Local to this module; downstream users get the structure map `schurToDsig`
explicitly rather than this instance. -/
noncomputable local instance chartDsigSchurLocAlgebra :
    Algebra (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (Localization.Away (chartDsig k d r hp hq)) :=
  (schurToDsig k d r hp hq).toRingHom.toAlgebra

/-- The local `SchurLoc`-algebra on `Away chartDsig` forms a scalar tower with `k` (the connecting
map `schurToDsig` is a `k`-algebra hom). -/
local instance chartDsigSchurLocIsScalarTower :
    IsScalarTower k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (Localization.Away (chartDsig k d r hp hq)) :=
  IsScalarTower.of_algebraMap_eq (fun x ↦ (schurToDsig k d r hp hq).commutes x |>.symm)

/-- **The top-left `SchurLoc`-LINEAR trivialization (S4b headline, top-left chart).** The top-left
chart total ring `Away chartDsig` is, OVER the in-chart Schur/base ring `SchurLoc` (acting via the
banked structure map `schurToDsig`), the standard fibre model `SchurLoc ⊗_k sweepFibreRing`:

> `Away chartDsig ≃ₐ[SchurLoc] SchurLoc ⊗_k sweepFibreRing`.

This upgrades the banked `k`-algebra `reducedFibre_chartDsig_tensorEquiv_reducedVariety` to a
`SchurLoc`-algebra equiv via `AlgEquiv.ofRingEquiv`, the `SchurLoc`-linearity being exactly
`reducedFibre_chartDsig_tensorEquiv_schurToDsig`. The product carries the LEFT-factor `SchurLoc`
structure; the source carries `schurToDsig`. -/
noncomputable def chartDsig_schurLocTensorEquiv :
    Localization.Away (chartDsig k d r hp hq)
      ≃ₐ[SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r]
        SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq :=
  AlgEquiv.ofRingEquiv (f := (reducedFibre_chartDsig_tensorEquiv_reducedVariety
      (k := k) d r hp hq).toRingEquiv)
    (fun x ↦ by
      -- `algebraMap SchurLoc (Away chartDsig) x = schurToDsig x`;
      -- `algebraMap SchurLoc (SchurLoc ⊗ F) x = x ⊗ₜ 1`.
      change reducedFibre_chartDsig_tensorEquiv_reducedVariety (k := k) d r hp hq
          (schurToDsig k d r hp hq x)
        = (algebraMap (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
            (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq) x)
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
      exact reducedFibre_chartDsig_tensorEquiv_schurToDsig d r hp hq x)

/-- **The top-left chart total ring is FLAT over `SchurLoc` (chartwise; the S3 `Flat π` payoff additionally needs projection compatibility).**
`Module.Flat SchurLoc (Away chartDsig)`: the genuine fibre-family flatness over the in-chart base,
chartwise. Transport of the standard model's `SchurLoc`-flatness (`standardFibreModel_flat`:
`SchurLoc ⊗_k sweepFibreRing` is `SchurLoc`-free) across the `SchurLoc`-LINEAR trivialization
`chartDsig_schurLocTensorEquiv` (via `Module.Flat.of_linearEquiv`). This is over the HONEST base
`SchurLoc` (the structure map `schurToDsig`), NOT the auxiliary-only flatness recorded in
`FibreFlatness.standardFibreModel_flat`. -/
theorem chartDsig_flat_over_schurLoc :
    Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (Localization.Away (chartDsig k d r hp hq)) :=
  haveI := standardFibreModel_flat (k := k) d r hp hq
  Module.Flat.of_linearEquiv (chartDsig_schurLocTensorEquiv d r hp hq).toLinearEquiv

end TopLeftFlat

/-! ## The per-pivot `SchurLoc`-linear trivialization + flatness over the base (S4b, every pivot)

For an arbitrary pivot `(s, t)` (with `σ, τ` carrying the first `r` rows/columns to it), the
structure map is the top-left `schurToDsig` carried along the gauge transport
`awayCongr (gaugeEquivSigma (pivotGauge σ τ))`. The banked per-pivot trivialization
`chartDsigAt_tensorEquiv` is then `SchurLoc`-linear, reduced to the top-left case by the gauge
`awayCongr` round-trip. -/

section PerPivotFlat

variable [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
  (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
  (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0))
  (σ : Equiv.Perm (Fin (d (Fin.last (N + 1))))) (τ : Equiv.Perm (Fin (d 0)))
  (hσ : ∀ i : Fin r, σ (Fin.castLE hp i) = s i) (hτ : ∀ j : Fin r, τ (Fin.castLE hq j) = t j)

/-- **The per-pivot chart total ring as a `SchurLoc`-algebra** (via `schurToDsigAt`). A plain `def`
(NOT a global instance: the structure map depends on the gauge `(σ, τ)`, which the type
`Away (chartDsigAt s t)` does not determine, so it must be supplied via `letI`). Downstream gets the
structure map `schurToDsigAt` explicitly. Marked `@[reducible]` (a class-typed `def` used in the
`letI` of the per-pivot statements: reducibility keeps the type-`letI` and body-`letI` defeq). -/
@[reducible] noncomputable def chartDsigAtSchurLocAlgebra :
    Algebra (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (Localization.Away (chartDsigAt (k := k) d r s t)) :=
  RingHom.toAlgebra (schurToDsigAt d r hp hq s t σ τ hσ hτ).toRingHom

/-- **The per-pivot `SchurLoc`-LINEAR trivialization (S4b headline, every pivot).** For each pivot
`(s, t)`, the chart total ring `Away (chartDsigAt s t)` is, OVER the in-chart Schur/base ring
`SchurLoc` (acting via `schurToDsigAt`, supplied as the `letI` algebra
`chartDsigAtSchurLocAlgebra`), the standard fibre model `SchurLoc ⊗_k sweepFibreRing`:

> `Away (chartDsigAt s t) ≃ₐ[SchurLoc] SchurLoc ⊗_k sweepFibreRing`.

This upgrades the banked `k`-algebra `chartDsigAt_tensorEquiv` to a `SchurLoc`-algebra equiv via
`AlgEquiv.ofRingEquiv`, the `SchurLoc`-linearity being `chartDsigAt_tensorEquiv_schurToDsigAt`. The
load-bearing over-base content S4 omitted: an iso of total rings respecting the base. -/
noncomputable def chartDsigAt_schurLocTensorEquiv :
    letI := chartDsigAtSchurLocAlgebra (k := k) d r hp hq s t σ τ hσ hτ
    Localization.Away (chartDsigAt (k := k) d r s t)
      ≃ₐ[SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r]
        SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq :=
  letI := chartDsigAtSchurLocAlgebra (k := k) d r hp hq s t σ τ hσ hτ
  AlgEquiv.ofRingEquiv (f := (chartDsigAt_tensorEquiv (k := k) d r hp hq s t σ τ hσ hτ).toRingEquiv)
    (fun x ↦ by
      change chartDsigAt_tensorEquiv (k := k) d r hp hq s t σ τ hσ hτ
          (schurToDsigAt d r hp hq s t σ τ hσ hτ x)
        = (algebraMap (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
            (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq) x)
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
      exact chartDsigAt_tensorEquiv_schurToDsigAt d r hp hq s t σ τ hσ hτ x)

/-- **The per-pivot chart total ring is FLAT over `SchurLoc` (chartwise, every pivot; the S3 `Flat π` payoff additionally needs projection compatibility).**
`Module.Flat SchurLoc (Away (chartDsigAt s t))` (over the `letI` structure-map algebra
`chartDsigAtSchurLocAlgebra`): the genuine fibre-family flatness over the in-chart base, chartwise,
at EVERY pivot. Transport of `standardFibreModel_flat` across the `SchurLoc`-LINEAR trivialization
`chartDsigAt_schurLocTensorEquiv` (via `Module.Flat.of_linearEquiv`). Over the HONEST base
`SchurLoc` (the structure map `schurToDsigAt`). -/
theorem chartDsigAt_flat_over_schurLoc :
    letI := chartDsigAtSchurLocAlgebra (k := k) d r hp hq s t σ τ hσ hτ
    Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (Localization.Away (chartDsigAt (k := k) d r s t)) :=
  letI := chartDsigAtSchurLocAlgebra (k := k) d r hp hq s t σ τ hσ hτ
  haveI := standardFibreModel_flat (k := k) d r hp hq
  Module.Flat.of_linearEquiv
    (chartDsigAt_schurLocTensorEquiv d r hp hq s t σ τ hσ hτ).toLinearEquiv

end PerPivotFlat

end DLNFibre.Core
