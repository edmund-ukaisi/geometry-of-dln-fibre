# Statement card — S5: over-base local-product-with-flatness capstone

> **Claim.** Over the rank-`= r` open of the DLN reduced fibre family, the family is, CHARTWISE and
> OVER the in-chart Schur-direction coordinate ring `SchurLoc` (via an honest structure map), the
> standard product `SchurLoc ⊗_k sweepFibreRing` AND is flat over `SchurLoc`. Pointwise: every prime
> `P` with universal-matrix residue-field rank `= r` sits in a pivot chart `basicOpen (chartDsigAt s t)`
> carrying a named structure map `φ : SchurLoc →ₐ[k] Away (chartDsigAt s t)` over which the chart total
> ring is `≃ₐ[SchurLoc] SchurLoc ⊗_k sweepFibreRing` and `Module.Flat SchurLoc (Away (chartDsigAt s t))`.

- **Lean (pointwise headline):** `DLNFibre.Core.reducedFibre_existsOverBaseProductChartAt_rankEq`
  (`lean/DLNFibre/Core/FibreBundleHeadline.lean` @ `39bded6ed669984fdee94d82922272615236f213`)
- **Lean (bundled structure):** `DLNFibre.Core.RankROpenOverBaseLocalProduct` +
  `DLNFibre.Core.reducedFibre_rankROpenOverBaseLocalProduct` (same file/SHA)
- **Lean (per-pivot datum):** `DLNFibre.Core.OverBaseChartDatum` + `DLNFibre.Core.overBaseChartDatum`
  (same file/SHA)

## Exact signatures

```lean
structure OverBaseChartDatum (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I : PivotDatum d r hp hq) where
  structMap : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →ₐ[k]
    Localization.Away (chartDsigAt (k := k) d r I.s I.t)
  triv :
    letI := structMap.toRingHom.toAlgebra
    Localization.Away (chartDsigAt (k := k) d r I.s I.t)
      ≃ₐ[SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r]
        SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq
  flat :
    letI := structMap.toRingHom.toAlgebra
    Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (Localization.Away (chartDsigAt (k := k) d r I.s I.t))

structure RankROpenOverBaseLocalProduct (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) where
  isRankLocus : ∀ P : PrimeSpectrum (sweepSigmaRing k d r),
    P ∈ rankROpen (k := k) d r ↔ (universalMatrixResidue d r P).rank = r
  cover : (⋃ st : (Fin r → Fin (d (Fin.last (N + 1)))) × (Fin r → Fin (d 0)),
        (PrimeSpectrum.basicOpen (chartDsigAt (k := k) d r st.1 st.2) :
          Set (PrimeSpectrum (sweepSigmaRing k d r)))) = rankROpen (k := k) d r
  chart : ∀ I : PivotDatum d r hp hq, OverBaseChartDatum (k := k) d r hp hq I

theorem reducedFibre_existsOverBaseProductChartAt_rankEq (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (P : PrimeSpectrum (sweepSigmaRing k d r))
    (hP : (universalMatrixResidue d r P).rank = r) :
    ∃ (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0)),
      P ∈ PrimeSpectrum.basicOpen (chartDsigAt (k := k) d r s t) ∧
      ∃ φ : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →ₐ[k]
          Localization.Away (chartDsigAt (k := k) d r s t),
        (letI := φ.toRingHom.toAlgebra;
          Nonempty (Localization.Away (chartDsigAt (k := k) d r s t)
            ≃ₐ[SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r]
              SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r
                ⊗[k] sweepFibreRing k d r hp hq)) ∧
        (letI := φ.toRingHom.toAlgebra;
          Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
            (Localization.Away (chartDsigAt (k := k) d r s t)))
```

(Context: `variable {k : Type} [Field k] [Infinite k] {N : ℕ}`.)

- **Gloss.** Fix a dimension tuple `d` and a rank `r` with `r ≤ d_N` (`hp`), `r ≤ d_0` (`hq`).
  - `OverBaseChartDatum I` is, at one pivot `I` (selectors `I.s, I.t` + gauge perms `I.σ, I.τ`),
    three bundled facts: an honest `k`-algebra map `structMap` from the Schur-direction ring `SchurLoc`
    into the localized chart total ring `Away (chartDsigAt I.s I.t)` (making the latter a
    `SchurLoc`-algebra); with that structure, a `SchurLoc`-algebra iso `triv` of the chart total ring
    with `SchurLoc ⊗_k sweepFibreRing`; and `flat`, that the chart total ring is a flat `SchurLoc`-module.
  - `RankROpenOverBaseLocalProduct` bundles, for fixed `(d, r)`: `isRankLocus` (a prime is in `rankROpen`
    iff its universal-matrix residue rank is `r`), `cover` (the per-pivot `basicOpen (chartDsigAt s t)`
    cover `rankROpen`), and `chart` (an `OverBaseChartDatum` at every pivot).
  - The pointwise theorem: for every prime `P` whose universal product matrix has rank exactly `r` over
    its residue field, there exist selectors `(s, t)` with `P ∈ basicOpen (chartDsigAt s t)` and an
    honest structure map `φ : SchurLoc →ₐ[k] Away (chartDsigAt s t)` such that, with the `φ`-induced
    `SchurLoc`-algebra structure, the chart total ring is `SchurLoc`-algebra-isomorphic to
    `SchurLoc ⊗_k sweepFibreRing` and is flat over `SchurLoc`.
- **Proved (unconditional).**
  - The full `RankROpenOverBaseLocalProduct` structure and the pointwise headline, sorry-free and
    axiom-clean `[propext, Classical.choice, Quot.sound]`.
  - Each chart datum is the genuine S4b over-base content: `structMap = schurToDsigAt`,
    `triv = chartDsigAt_schurLocTensorEquiv` (a `≃ₐ[SchurLoc]`, not a bare `≃ₐ[k]`),
    `flat = chartDsigAt_flat_over_schurLoc`. This is a strict upgrade of the S4 headline
    `reducedFibre_existsProductChartAt_rankEq` (which only gave `Nonempty (… ≃ₐ[k] …)`).
- **Assumed (hypotheses, same as S4).** `hp : r ≤ d_N`, `hq : r ≤ d_0`, `[Infinite k]`, and the
  per-point hypothesis `hP : (universalMatrixResidue d r P).rank = r`. These match the S1/S4 reviewed
  hypothesis class; `hP` is exactly the S1 rank-locus characterization, so it is reachable (the
  top-left chart witnesses non-emptiness).
- **Cited.** none (all fields are banked in-repo S1/S4/S4b results).
- **Deferred (NAMED OPEN ITEMS — read before reusing).**
  1. **Chart-base bridge (a real build, AHEAD of R1).** The base of the trivialization + flatness is
     `SchurLoc` = the in-chart Schur-direction coordinate ring (`Localization.Away (detSchurS …)`),
     which is a DIFFERENT ring from the actual base-restriction of `sweepSigmaRing` to
     `basicOpen (chartDsigAt s t)` (= `Away (chartDsigAt s t)`, a localization OF `sweepSigmaRing`).
     There is NO proven identification `SchurLoc ≅ (sweepSigmaRing restricted to basicOpen(chartDsigAt))`
     with structure-map compatibility. Until that bridge is built, the flatness/triviality is honestly
     only over `SchurLoc`, NOT over `rankROpen ⊆ Spec(sweepSigmaRing)`. The Lean wording is "over
     `SchurLoc`" throughout — never "flat over `rankROpen`" / "flat over `sweepSigmaRing`".
  2. **Global `Flat π` / `FiberBundle` over all of `rankROpen` (R1).** This is CHARTWISE only. A single
     global flatness-of-`π` or fibre-bundle statement over the whole `rankROpen` needs the target-side
     overlap-gluing cocycle (roadmap R1 `targetOverlapTransition`) to assemble the per-chart data; not
     claimed here. (Whether global flatness as a property globalizes from the chartwise data without R1
     is a separate question assessed elsewhere.)
  3. No scheme-morphism / continuity / sheaf content: `structMap` is the in-chart *ring* map only.
- **Route.** Mirror the S4 assembly `reducedFibre_existsProductChartAt_rankEq`: S1 puts `P` in
  `rankROpen = ⋃ basicOpen (chartDsigAt s t)`; `pivotDatumOfMemBasicOpen` turns chart membership into a
  `PivotDatum I` (membership forces selector injectivity). Then present the existential at `I.s, I.t`
  (where the S4b over-base data — `schurToDsigAt`, `chartDsigAt_schurLocTensorEquiv`,
  `chartDsigAt_flat_over_schurLoc` — lives natively), transporting only the cheap membership Prop across
  `hI : chartDsigAt I.s I.t = chartDsigAt st.1 st.2`; the heavy structure-map algebra is never `▸`-cast
  (avoids the `isDefEq`/`whnf` heartbeat blowup an `hrw ▸` on the over-base data triggers).
- **Status.** sorry-free + reviewed (reviewer PASS + decorrelated Codex consult concurring:
  over-base content genuine — honest `schurToDsigAt`, real `≃ₐ[SchurLoc]` B-linearity proved
  separately, both conjuncts over the same bound `φ`'s algebra, no self-reference; non-vacuous;
  no overclaim, both open items named).
