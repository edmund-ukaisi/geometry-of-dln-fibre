# S4b — the `SchurLoc`-linear (over-base) trivialization + fibre-family flatness over the base

The convergent keystone S3 (flatness) and S4 (local triviality) both needed: upgrade the banked
per-pivot trivialization from a **`k`-algebra** equiv to a **`SchurLoc`-algebra** equiv (over the
in-chart Schur/base coordinate ring), then read off the genuine fibre-family flatness over the base,
chartwise.

Module: `lean/DLNFibre/Core/FibreOverBaseTriv.lean` (new). One additive helper lemma added to
`lean/DLNFibre/Core/FibreBundleReduced.lean` (the keystone base-change's action on a generator —
provable only where the def's local product-algebra instance is in scope).

---

## The crux

> **Claim.** The keystone tensor base-change `reducedFibre_chartGfib_tensorEquiv_reducedVariety`
> (`Away chartGfib ≃ₐ[k] SchurLoc ⊗_k sweepFibreRing`) sends the connecting algebra map
> `schurToGfib x` to the left tensor factor `x ⊗ₜ 1` — i.e. it respects the `SchurLoc`-action.
>
> - **Lean:** `DLNFibre.Core.reducedFibre_chartGfib_tensorEquiv_schurToGfib`
>   (`lean/DLNFibre/Core/FibreOverBaseTriv.lean`)
> - **Gloss.** For every `x : SchurLoc`, `tensorEquiv (schurToGfib x) = x ⊗ₜ 1`. `schurToGfib` is the
>   banked connecting map `SchurLoc →ₐ[k] Away chartGfib` (localization of the coefficient
>   base-change at `detSchurS`); the right side is the left-factor structure map of `SchurLoc ⊗_k F`.
> - **Proved.** Unconditionally (field `k`, `[Infinite k]`). Via `Localization.algHom_ext` +
>   `MvPolynomial.algHom_ext`, reduced to the single generator lemma
>   `mvPolynomialAwayMapTensorAlgEquiv_algebraMap_X` (added to `FibreBundleReduced`) +
>   `schurToGfib_algebraMap`.
> - **Assumed.** none beyond `[Field k] [Infinite k]`.
> - **Cited.** none — Mathlib `algebraTensorAlgEquiv_symm_map`, `IsLocalization.algEquivOfAlgEquiv_eq`.
> - **Deferred.** none.
> - **Status.** sorry-free, axiom-clean.

---

## The over-base trivialization (S4b headline) — top-left and every pivot

> **Claim.** Each chart total ring is, OVER the in-chart Schur/base ring `SchurLoc` (acting via an
> honest structure map), the standard fibre model `SchurLoc ⊗_k sweepFibreRing`:
> `Away (chartDsig) ≃ₐ[SchurLoc] SchurLoc ⊗_k sweepFibreRing` (top-left), and the same at every pivot
> `(s, t)` for `Away (chartDsigAt s t)`.
>
> - **Lean (top-left):** `DLNFibre.Core.chartDsig_schurLocTensorEquiv`
> - **Lean (per-pivot):** `DLNFibre.Core.chartDsigAt_schurLocTensorEquiv`
>   (over the `letI` structure-map algebra `chartDsigAtSchurLocAlgebra`)
>   (`lean/DLNFibre/Core/FibreOverBaseTriv.lean`)
> - **Gloss.** The `SchurLoc`-action on the source chart total ring is the HONEST composite structure
>   map: top-left `schurToDsig = chartPhiLoc ∘ schurToGfib` (the banked connecting map pulled back
>   through the deep chart); per-pivot `schurToDsigAt = awayCongr (gaugeEquivSigma (pivotGauge σ τ)) ∘
>   schurToDsig` (carried along the row/column-permutation gauge). The equiv is the banked
>   `k`-algebra trivialization promoted to `≃ₐ[SchurLoc]` via `AlgEquiv.ofRingEquiv`, the
>   `SchurLoc`-linearity being `reducedFibre_chartDsig_tensorEquiv_schurToDsig` /
>   `chartDsigAt_tensorEquiv_schurToDsigAt`.
> - **Proved.** Unconditionally. The structure map is independent of the equiv being upgraded (not a
>   pullback along it) — non-circular. Per-pivot linearity reduces to the top-left via the deep-chart
>   round-trip and the gauge `awayCongr` cancellation; top-left reduces to the crux.
> - **Assumed.** `[Field k] [Infinite k]`; pivot data `(s, t, σ, τ, hσ, hτ)` with `σ, τ` carrying the
>   first `r` rows/columns to `(s, t)`.
> - **Cited.** none.
> - **Deferred.** A single GLOBAL `Flat π` / `FiberBundle` morphism over all of `rankROpen`
>   additionally needs the overlap-gluing cocycle (R1 `targetOverlapTransition`) — roadmapped, NOT
>   claimed. This card is the CHARTWISE over-base trivialization, at every pivot.
> - **Status.** sorry-free, axiom-clean.

---

## The fibre-family flatness over the base (S3 payoff) — top-left and every pivot

> **Claim.** Each chart total ring is FLAT over the in-chart base `SchurLoc` (the genuine
> fibre-family flatness over the base, chartwise): `Module.Flat SchurLoc (Away (chartDsig))`
> (top-left) and `Module.Flat SchurLoc (Away (chartDsigAt s t))` at every pivot.
>
> - **Lean (top-left):** `DLNFibre.Core.chartDsig_flat_over_schurLoc`
> - **Lean (per-pivot):** `DLNFibre.Core.chartDsigAt_flat_over_schurLoc`
>   (over the `letI` structure-map algebra `chartDsigAtSchurLocAlgebra`)
>   (`lean/DLNFibre/Core/FibreOverBaseTriv.lean`)
> - **Gloss.** Over the HONEST base `SchurLoc` (the structure map `schurToDsig` / `schurToDsigAt`,
>   NOT the auxiliary-only base of `FibreFlatness.standardFibreModel_flat`), the chart total ring is a
>   flat `SchurLoc`-module. The standard model `SchurLoc ⊗_k sweepFibreRing` is `SchurLoc`-free
>   (`standardFibreModel_flat`); its flatness transports across the `SchurLoc`-LINEAR trivialization
>   (`Module.Flat.of_linearEquiv`).
> - **Proved.** Unconditionally, CHARTWISE: the chart total ring is flat over `SchurLoc` via the named
>   structure map `schurToDsigAt`. This is **not** the S3 target `Flat π : mult⁻¹(rankROpen) → rankROpen`
>   itself — `SchurLoc` is the in-chart base DIRECTION and `Spec(sweepSigmaRing)` is the source/total;
>   reading this as genuine fibre-family flatness over the base needs projection compatibility (Deferred).
> - **Assumed.** as above.
> - **Cited.** none.
> - **Deferred.** (i) **projection compatibility** — that `schurToDsigAt` is the pullback of `mult`'s
>   projection from the target/base rank-chart (the prerequisite for reading `SchurLoc`-flatness as
>   genuine fibre-family flatness over the base); (ii) the global single-morphism `Flat π` (overlap
>   cocycle R1).
> - **Status.** sorry-free, axiom-clean.

---

## Supporting / structure-map facts (all sorry-free, axiom-clean)

- `schurToDsigAt` — the per-pivot honest structure map `SchurLoc →ₐ[k] Away (chartDsigAt s t)`.
- `chartDsigAtSchurLocAlgebra` — the per-pivot `SchurLoc`-algebra on the chart total ring (a `def`,
  not a global instance: the gauge `(σ, τ)` is not determined by the type `Away (chartDsigAt s t)`).
- `chartLocalizedAlgEquiv_schurToDsig` — the deep-chart round-trip used to reduce top-left to the crux.
- `mvPolynomialAwayMapTensorAlgEquiv_algebraMap_X` (in `FibreBundleReduced`) — the keystone
  base-change's action on a single variable `X v`; the only computational handle on the opaque
  `mvPolynomialAwayMapTensorAlgEquiv` (built via `IsLocalization.algEquivOfAlgEquiv`), provable only
  in the section that owns the local product-algebra instance.

## Exact signatures

```lean
theorem reducedFibre_chartGfib_tensorEquiv_schurToGfib (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (x : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) :
    reducedFibre_chartGfib_tensorEquiv_reducedVariety (k := k) d r hp hq (schurToGfib k d r hp hq x)
      = x ⊗ₜ[k] (1 : sweepFibreRing k d r hp hq)

noncomputable def chartDsig_schurLocTensorEquiv (d r) (hp hq) :
    Localization.Away (chartDsig k d r hp hq)
      ≃ₐ[SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r]
        SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq

theorem chartDsig_flat_over_schurLoc (d r) (hp hq) :
    Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (Localization.Away (chartDsig k d r hp hq))

noncomputable def chartDsigAt_schurLocTensorEquiv (d r) (hp hq) (s t σ τ hσ hτ) :
    letI := chartDsigAtSchurLocAlgebra (k := k) d r hp hq s t σ τ hσ hτ
    Localization.Away (chartDsigAt (k := k) d r s t)
      ≃ₐ[SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r]
        SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq

theorem chartDsigAt_flat_over_schurLoc (d r) (hp hq) (s t σ τ hσ hτ) :
    letI := chartDsigAtSchurLocAlgebra (k := k) d r hp hq s t σ τ hσ hτ
    Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (Localization.Away (chartDsigAt (k := k) d r s t))
```

`#print axioms` for all seven deliverables (+ the helper) = `[propext, Classical.choice, Quot.sound]`.

**Commit SHA:** landed `caa96288` on `expedition/fibration-geometry` (PR #12); docstring fences refined
in later review-round commits on the same branch.
