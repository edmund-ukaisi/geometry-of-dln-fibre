# Thread 21 — the `e_β` ↔ ambient bridge (B3-4) — statement card

**Status: sorry-free (pending reviewer fidelity).** Module
`lean/DLNFibre/Core/FibreBundleLocallyTrivial.lean`. Whole library green; all four headlines
axiom-clean `[propext, Classical.choice, Quot.sound]` (gated via `#print axioms`).

**Scope verdict (honest, per brief): PARTIAL.** This is the genuine **top-left** `e_β` ↔ ambient
bridge + the local-trivialization *datum* shape with the top-left chart instantiated. It is **NOT**
named `locallyTrivial` and does NOT earn that name: only one chart of the would-be atlas is supplied.
The per-pivot trivialization `e_{s,t}` is disclaimed in-module as the remaining cost.

---

## Card 1 — the seam between the two coordinate rings

> **Claim.** The thread-19 ambient minor polynomial at the top-left pivot
> `detMinorPoly (topLeftRows) (topLeftCols)` (in single-matrix coords `MvPolynomial (Fin p × Fin q)
> k`) is the coordinate rename, along `repStratumEquiv : RepCoord (dStratum q p) ≃ Fin p × Fin q`,
> of the chart-side single-matrix pivot minor `detPivotPoly q p r` (in stratum coords
> `MvPolynomial (RepCoord (dStratum q p)) k`).
>
> - **Lean:** `DLNFibre.Core.detMinorPoly_topLeft_rename`
>   (`lean/DLNFibre/Core/FibreBundleLocallyTrivial.lean`)
> - **Gloss.** `renameEquiv repStratumEquiv (detPivotPoly q p r hp hq) = detMinorPoly (topLeftRows
>   p r hp) (topLeftCols q r hq)`. Both sides are the determinant of the same generic single-matrix
>   minor; the generic entries `X (a,b)` (ambient) and `X ⟨0,(a,b)⟩` (stratum) correspond under
>   `repStratumEquiv`. This is the missing seam tying thread-19's ambient principal-open presentation
>   `D(detMinorPoly)` to the chart side.
> - **Proved.** The rename identity, unconditional, any field `k : Type` (universe 0).
> - **Assumed.** `r ≤ p`, `r ≤ q` (the pivot selectors).
> - **Cited.** none.
> - **Deferred.** the per-pivot (`s,t ≠` top-left) analogue.
> - **Status.** sorry-free.

## Card 2 — the bridge `AlgHom` + its denominator fidelity

> **Claim.** The chart-side pivot minor `detPivotPoly` is carried by the base→total transport
> `baseLocMap` to the deep total pivot minor `ΔPdeep d r`, whose quotient class is `chartDsig` — the
> element `e_β` inverts. The bridge `AlgHom` connects the two **inverted** localizing elements.
>
> - **Lean:** `DLNFibre.Core.topLeftBaseToChartAway` +
>   `DLNFibre.Core.topLeftBaseToChartAway_algebraMap_detPivot`
>   (`lean/DLNFibre/Core/FibreBundleLocallyTrivial.lean`)
> - **Gloss.** `topLeftBaseToChartAway : Away (detPivotPoly q p r) →ₐ[k] Away (ΔPdeep d r)`
>   (= `baseLocMap`), and the fidelity theorem: it sends `algebraMap _ _ (detPivotPoly)` to
>   `algebraMap _ _ (ΔPdeep)`. So the bridge identifies the inverted denominators of the two
>   presentations, not merely the ring types.
> - **Proved.** the `AlgHom` exists; it carries the localized ambient pivot minor to the localized
>   deep pivot minor (via `baseLocMap_algebraMap` + `deepBaseComap_detPivot`).
> - **Assumed.** `r ≤ d (last N)`, `r ≤ d 0`; `k : Type`.
> - **Cited.** none (reuses banked `Core.DeepChartRing` transports).
> - **Deferred.** that the bridge is an `AlgEquiv` (it is an `AlgHom`; the deep-vs-ambient comparison
>   is not shown to be invertible here), and the per-pivot analogue.
> - **Status.** sorry-free.

## Card 3 — the local-trivialization datum + the top-left instantiation

> **Claim.** A locally trivial bundle chart is the data of a principal-open base element + a
> localized trivialization `Total ≃ₐ[k] BaseLoc ⊗_k Fibre`. The **top-left** datum is genuinely
> instantiated: `chartElt = chartDsig`, `trivialization = e_β`-composite (thread-11
> `reducedFibre_chartDsig_tensorEquiv_reducedVariety`).
>
> - **Lean:** `DLNFibre.Core.LocalTrivializationDatum` (structure) +
>   `DLNFibre.Core.topLeftLocalTrivializationDatum`
>   (`lean/DLNFibre/Core/FibreBundleLocallyTrivial.lean`)
> - **Gloss.** the structure bundles `chartElt : Base` and `trivialization : Total ≃ₐ[k] BaseLoc ⊗_k
>   Fibre`; the top-left instance has `Total = Away chartDsig`, `BaseLoc = SchurLoc`, `Fibre =
>   sweepFibreRing`, the trivialization the genuine `e_β`-then-tensor composite.
> - **Proved.** the structure + the genuine top-left instance (data, non-vacuous by construction).
> - **Assumed.** `[Infinite k]` (the chart `e_β`); `r ≤ d (last (N+1))`, `r ≤ d 0`.
> - **Cited.** none.
> - **Deferred.** **the atlas**: a FAMILY of these data covering `Mat^{=r}` (all pivots `s,t`) + the
>   ambient cocycle (`awayOverlapTransition`) shown to transport onto the per-pivot trivializations.
>   This is exactly what a `locallyTrivial` name requires and is NOT built. Building `e_{s,t}`
>   requires re-deriving the ~250-LoC deep chart per pivot, OR proving that the product-coordinate
>   permutation conjugates the entire deep chart construction (`vanishingIdeal Σ^r`, `ΔPdeep`, every
>   Schur generator) to its `(s,t)` analogue — a conjugation skeleton not established here.
> - **Status.** sorry-free.

---

## Why NOT `locallyTrivial` (the honest negative + cost)

The bundle now has (banked across threads): the per-minor open cover of `Mat^{=r}` (#18), the
per-minor `k`-point chart family (#18), the genuine ambient ring-level transition cocycle (#19), the
single top-left deep trivialization `e_β` (#11), and now (#21) **the genuine identification of the
top-left ambient chart with the deep-chart presentation `e_β` inverts**. The one missing rung to
`locallyTrivial` is the **per-pivot trivialization** `e_{s,t}` for `(s,t) ≠` top-left, plus the
cocycle transport onto it. Codex (xhigh, decorrelated) ranked the candidate scopes and judged the
cheap "transport `e_β` along a coordinate permutation" route **plausible but not automatic**: it
requires first proving the conjugation skeleton (that permuting end-factor rows/cols conjugates the
*whole* deep chart construction, not merely the determinant). That is a separate multi-module build.

**Universe note (pitfall confirmed by Codex).** `detMinorPoly`/`minorChartEquiv` pin `k : Type`
(universe 0) via `pivotRankChart` reuse; `e_β` is universe-polymorphic. The bridge is stated at
`k : Type`, the common ground (`ℂ` is `Type 0`, harmless for DLN).
