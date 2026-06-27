/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreBundleTransition
import DLNFibre.Core.FibreBundleReduced
import DLNFibre.Core.DeepChartRing

/-!
# `DLNFibre.Core.FibreBundleLocallyTrivial` — the `e_β` ↔ ambient bridge (B3-4)

Thread 18 built the per-minor open cover of `Mat^{=r}` + the per-minor chart family; thread 19
built the genuine ring-level transition cocycle on the **ambient** `O(Mat) = MvPolynomial (Fin p ×
Fin q) k` principal-open cover (`awayOverlapTransition`, `minorChartTransition`). The deep Schur
trivialization `e_β = chartLocalizedAlgEquiv` (`Away chartDsig ≃ₐ[k] Away chartGfib`) lives in deep
**product-representation** chart coordinates and is built only at the **top-left pivot** of one
`(d, r)`. The sole remaining gap to a `locallyTrivial` name is the bridge between these two
presentations.

## What is built (honest scope — the genuine top-left bridge)

This module identifies the ambient **top-left** per-minor chart with the deep-chart presentation
that `e_β` inverts, via the **already-built** base→total transport of `Core.DeepChartRing`:

- `detMinorPoly_topLeft_rename` — the genuine seam between the two coordinate rings. The ambient
  minor polynomial `detMinorPoly (top-left s) (top-left t)` (in single-matrix coords
  `MvPolynomial (Fin p × Fin q) k`, thread 19) is the coordinate rename
  `renameEquiv repStratumEquiv` of the chart-side single-matrix pivot minor `detPivotPoly q p r`
  (in stratum coords `MvPolynomial (RepCoord (dStratum q p)) k`). Both are the determinant of the
  same generic single-matrix minor; they differ only by the relabeling `RepCoord (dStratum q p) ≃
  Fin p × Fin q`.

- `topLeftBaseToChartAway` — assembles the bridge `AlgHom`. The chart-side `detPivotPoly` is carried
  by `Core.deepBaseComap`/`Core.baseLocMap` to the **deep total** pivot minor `ΔPdeep d r`
  (`deepBaseComap_detPivot`), whose quotient class is exactly `chartDsig` (the element `e_β`
  inverts). So `Localization.Away (detPivotPoly q p r) →ₐ[k] Localization.Away (ΔPdeep d r)`
  (= `baseLocMap`), composed downstream of the rename, gives a `k`-algebra map from the localized
  ambient top-left base chart into the localized deep total chart on which `e_β` acts.

- `LocalTrivializationDatum` / `topLeftLocalTrivializationDatum` — the SHAPE of a locally trivial
  bundle datum (a principal-open base chart + a localized trivialization `AlgEquiv` to a product
  `base ⊗ fibre`), with the **top-left datum genuinely instantiated** from `e_β` + the thread-11
  tensor package. This is one chart of the would-be atlas, not the atlas.

## What is NOT built (disclaimed — why this is NOT named `locallyTrivial`)

A genuine `locallyTrivial` bundle over `Mat^{=r}` needs a trivialization on **every** member of the
per-minor cover (all pivots `(s, t)`), not just the top-left one, plus the ambient cocycle
(`awayOverlapTransition`) shown to transport onto those per-pivot trivializations. The per-pivot
trivialization `e_{s,t}` is **not** built here: the deep chart `e_β` is constructed only at the
top-left pivot, and obtaining `e_{s,t}` requires either re-deriving the ~250-LoC chart per pivot, or
proving that the product-coordinate permutation (permuting the rows of the final factor / columns of
the first factor of the generic product) conjugates the **entire** deep chart construction
(`vanishingIdeal Σ^r`, `ΔPdeep`, and every Schur generator inside `chartLocalizedAlgEquiv`) to its
`(s, t)` analogue — a conjugation skeleton not established here. So this is the **top-left chart**
of the bundle + the explicit cover/cocycle (banked in threads 18/19), with the per-pivot
trivialization the honest remaining cost. Accordingly **not** named `locallyTrivial`.

**Universe note.** `detMinorPoly`/`minorChartEquiv` (thread 18/19) pin `k : Type` (universe 0) via
the `pivotRankChart` reuse; `chartLocalizedAlgEquiv` is universe-polymorphic. The bridge is stated
at `k : Type` (the common ground; `ℂ` is `Type 0`, so this is harmless for the DLN application).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix
open scoped TensorProduct

universe u

/-! ## The seam: the ambient top-left minor polynomial is the rename of the chart pivot minor -/

section Seam

variable {k : Type} [Field k]

/-- **The top-left row selector** `Fin r → Fin p`, the inclusion of the first `r` rows. -/
def topLeftRows (p r : ℕ) (hp : r ≤ p) : Fin r → Fin p := fun i ↦ Fin.castLE hp i

/-- **The top-left column selector** `Fin r → Fin q`, the inclusion of the first `r` columns. -/
def topLeftCols (q r : ℕ) (hq : r ≤ q) : Fin r → Fin q := fun j ↦ Fin.castLE hq j

/-- **The genuine seam between the ambient and the chart coordinate rings.** The thread-19 ambient
minor polynomial at the top-left pivot — `detMinorPoly (topLeftRows) (topLeftCols)`, a determinant
in single-matrix coords `MvPolynomial (Fin p × Fin q) k` — is the coordinate rename, along
`repStratumEquiv : RepCoord (dStratum q p) ≃ Fin p × Fin q`, of the chart-side single-matrix pivot
minor `detPivotPoly q p r`. Both are the determinant of the same generic single-matrix minor; the
generic matrix entries `X (a, b)` (ambient) and `X ⟨0, (a, b)⟩` (stratum) correspond under
`repStratumEquiv`. -/
theorem detMinorPoly_topLeft_rename (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    (renameEquiv k (repStratumEquiv q p))
        (detPivotPoly (k := k) q p r hp hq)
      = detMinorPoly (k := k) (topLeftRows p r hp) (topLeftCols q r hq) := by
  -- both sides are `det` of the same generic-minor matrix; the algebra map commutes with `det`
  -- (`AlgEquiv.map_det`), and entrywise `renameEquiv repStratumEquiv (X ⟨0,(a,b)⟩) = X (a,b)`.
  rw [detPivotPoly, detMinorPoly, AlgEquiv.map_det]
  congr 1
  funext i j
  rw [AlgEquiv.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, Matrix.submatrix_apply,
    multPoly_stratum_apply, renameEquiv_apply, rename_X, Matrix.mvPolynomialX_apply]
  rfl

end Seam

/-! ## The bridge `AlgHom`: ambient top-left base chart → deep total chart -/

section Bridge

variable {k : Type} [Field k] {N : ℕ}

/-- **The bridge `AlgHom` `Localization.Away (detPivotPoly q p r) →ₐ[k] Localization.Away (ΔPdeep d
r)`.** The chart-side single-matrix pivot minor `detPivotPoly` is carried by the base→total
transport `baseLocMap` to the deep total pivot minor `ΔPdeep d r` — the element whose quotient class
is `chartDsig`, the localizing element `e_β` inverts. This is `Core.baseLocMap`, re-exported as
the bridge from the ambient top-left base chart's localized ring to the deep total chart's. -/
noncomputable def topLeftBaseToChartAway (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)
      →ₐ[k] Localization.Away (ΔPdeep (k := k) d r hp hq) :=
  baseLocMap d r hp hq

/-- **The bridge connects the two inverted localizing elements.** Applying the bridge `AlgHom` to
the localized ambient top-left pivot minor `algebraMap _ _ (detPivotPoly q p r)` (the element the
base chart `D(detMinorPoly)` inverts) lands on the localized deep total pivot minor
`algebraMap _ _ (ΔPdeep d r)` — the element whose quotient class is `chartDsig`, what `e_β` inverts.
So the bridge genuinely identifies the inverted denominators of the two presentations, not just the
ring types. (`baseLocMap_algebraMap` carries `algebraMap x` to `algebraMap (deepBaseComap d x)`;
`deepBaseComap_detPivot` evaluates `deepBaseComap d (detPivotPoly) = ΔPdeep`.) -/
theorem topLeftBaseToChartAway_algebraMap_detPivot (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    topLeftBaseToChartAway d r hp hq
        (algebraMap (MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k)
          (Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq))
          (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq))
      = algebraMap (MvPolynomial (RepCoord d) k)
          (Localization.Away (ΔPdeep (k := k) d r hp hq)) (ΔPdeep (k := k) d r hp hq) := by
  rw [topLeftBaseToChartAway, baseLocMap_algebraMap, deepBaseComap_detPivot]

end Bridge

/-! ## The local-trivialization datum (the shape of a `locallyTrivial` bundle chart) -/

section Datum

variable (k : Type u) [Field k]

/-- **A local-trivialization datum for a principal-open chart.** The data of ONE chart of a locally
trivial fibre bundle over an affine base with coordinate ring `Base`: a principal-open base element
`chartElt : Base` and a `k`-algebra trivialization of the localized chart total ring `Total` as a
tensor product `BaseLoc ⊗_k Fibre` (the local product structure), where `BaseLoc` is the localized
base direction and `Fibre` the fibre coordinate ring. A `locallyTrivial` bundle is a FAMILY of these
covering the base, with a compatible transition cocycle on overlaps; this structure captures a
single chart's worth of that data. -/
structure LocalTrivializationDatum
    (Base : Type u) [CommRing Base] [Algebra k Base]
    (Total : Type u) [CommRing Total] [Algebra k Total]
    (BaseLoc : Type u) [CommRing BaseLoc] [Algebra k BaseLoc]
    (Fibre : Type u) [CommRing Fibre] [Algebra k Fibre] where
  /-- The principal-open base element cutting the chart `D(chartElt)`. -/
  chartElt : Base
  /-- The localized chart trivialization: `Total ≃ₐ[k] BaseLoc ⊗_k Fibre`. -/
  trivialization : Total ≃ₐ[k] BaseLoc ⊗[k] Fibre

end Datum

/-! ## The top-left datum, genuinely instantiated from `e_β` + the tensor package -/

section TopLeftDatum

variable {k : Type} [Field k] {N : ℕ}

/-- **The top-left local-trivialization datum, genuinely instantiated.** The chart element is the
chart-side pivot minor `chartDsig` (the deep total pivot minor's class), and the trivialization is
the thread-11 composite `reducedFibre_chartDsig_tensorEquiv_reducedVariety`
(`e_β` then the schur-side tensor package), which exhibits the localized deep chart total ring
`Away chartDsig` as the product `SchurLoc ⊗_k sweepFibreRing` of the local matrix direction with
the **reduced** fibre coordinate ring. This is ONE chart of the would-be bundle atlas — the
top-left pivot — **not** the full atlas (the per-pivot trivializations are unbuilt; see the module
docstring). Needs `[Infinite k]` (the chart `e_β`). -/
noncomputable def topLeftLocalTrivializationDatum [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    LocalTrivializationDatum k
      (sweepSigmaRing k d r)
      (Localization.Away (chartDsig k d r hp hq))
      (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (sweepFibreRing k d r hp hq) where
  chartElt := chartDsig k d r hp hq
  trivialization := reducedFibre_chartDsig_tensorEquiv_reducedVariety d r hp hq

end TopLeftDatum

/-! ## Non-vacuity witnesses

The seam fires on a concrete single matrix; the bridge and the datum fire at an abstract
`[Infinite k]` field and dimension vector (the deep chart `e_β` needs `[Infinite k]`, kept abstract
throughout the route as in `Core.FibreBundleReduced`). -/

section Witness

/-- **Seam witness.** At `q = p = 2`, `r = 1` over `ℚ`, the ambient top-left minor polynomial is the
rename of the chart pivot minor (a concrete instance of `detMinorPoly_topLeft_rename`). -/
example (h : (1 : ℕ) ≤ 2) :
    (renameEquiv ℚ (repStratumEquiv 2 2)) (detPivotPoly (k := ℚ) 2 2 1 h h)
      = detMinorPoly (k := ℚ) (topLeftRows 2 1 h) (topLeftCols 2 1 h) :=
  detMinorPoly_topLeft_rename 2 2 1 h h

/-- **Datum witness.** The top-left local-trivialization datum is genuine data — its chart elt is
`chartDsig` and its trivialization is the `e_β`-composite — available over any `[Infinite k]` field
and dimension vector. (Non-vacuous: it is constructed, not asserted.) -/
noncomputable example {k : Type} [Field k] [Infinite k] {N : ℕ}
    (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (topLeftLocalTrivializationDatum d r hp hq).chartElt = chartDsig k d r hp hq :=
  rfl

end Witness

end DLNFibre.Core
