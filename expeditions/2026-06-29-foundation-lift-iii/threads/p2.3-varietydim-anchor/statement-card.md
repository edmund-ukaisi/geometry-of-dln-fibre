# Statement card — P2.3 abstract `varietyDim = trdeg` anchor (A4.1)

The squeeze's **lower anchor** lifted to the P2.2 carrier `AffineGVariety`, with the DLN form
re-derived from it. Scope: the A4.1 anchor + the A0 bridge only (NOT A4.4 — that combines with the
δ-rank bound B1, which is P2.4).

---

## Anchor (orbit-coordinate-algebra form)

> **Claim.** For an abstract affine-`G`-variety carrier `G : AffineGVariety k` with **finite** ambient
> coordinate index `G.ρ`, the orbit coordinate algebra `G.pullback.range = k[fρ]` (a f.g. `k`-domain)
> has Krull dimension equal to its transcendence degree over `k`.
>
> - **Lean:** `AlgebraicGeometry.Group.Orbit.AffineGVariety.ringKrullDim_pullback_range_unbotD_eq_trdeg_toNat`
>   (`lean/DLNFibre/Core/AlgebraicGeometry/Group/Orbit/Dimension.lean` @ `<commit-sha>`)
> - **Gloss.** `[Finite G.ρ] ⊢ (ringKrullDim G.pullback.range).unbotD 0 = (Algebra.trdeg k G.pullback.range).toNat`.
>   `G.pullback = aeval fρ : MvPolynomial G.ρ k →ₐ[k] G.R`; its range is `Algebra.adjoin k (range fρ)`.
> - **Proved.** The `dim = trdeg` equality, in `.unbotD 0` / `.toNat` (`ℕ`) form, on the abstract carrier.
>   `G.pullback.range` is a f.g. `k`-domain: finite-generation from `[Finite G.ρ]` (so
>   `MvPolynomial G.ρ k` is `Algebra.FiniteType k`, range via `of_surjective` — the new instance
>   `finiteType_pullback_range`); domain automatically (subalgebra of the domain `G.R`).
> - **Assumed.** `[Finite G.ρ]` — the finite-generation input. Carried here, NOT on the base carrier
>   (`Orbit/Basic.lean` deliberately keeps `ρ` finiteness off the irreducibility layer).
> - **Cited.** none new. Reduces to the Phase-1 `Dimension.ringKrullDim_eq_trdeg_of_fg_domain`
>   (Noether normalization + `trdeg`-API, already in-repo, axiom-clean).
> - **Deferred.** none.
> - **Status.** sorry-free.

## Anchor (variety-dimension form, with the A0 bridge)

> **Claim.** Given additionally a point set `Z ⊆ G.ρ → k` whose vanishing ideal **is** the pullback
> kernel (the A0 / L6.4 orbit↔kernel equality), `varietyDim Z = trdeg k (k[fρ])`.
>
> - **Lean:** `AlgebraicGeometry.Group.Orbit.AffineGVariety.varietyDim_eq_trdeg_of_eq_ker`
>   (`lean/DLNFibre/Core/AlgebraicGeometry/Group/Orbit/Dimension.lean` @ `<commit-sha>`)
> - **Gloss.** `[Finite G.ρ] → (vanishingIdeal k Z = RingHom.ker G.pullback.toRingHom) →`
>   `varietyDim Z = ((Algebra.trdeg k G.pullback.range).toNat : ℕ∞)`. `varietyDim Z` is
>   `(ringKrullDim (MvPolynomial G.ρ k ⧸ vanishingIdeal Z)).unbotD 0`.
> - **Proved.** `varietyDim Z = trdeg`-of-orbit-coordinate-algebra, transported from the
>   orbit-coordinate-algebra form through the first-iso `Ideal.quotientKerEquivRange G.pullback`
>   (`MvPolynomial G.ρ k ⧸ ker μ* ≃ₐ[k] μ*.range`) via `ringKrullDim_eq_of_ringEquiv`.
> - **Assumed.** `[Finite G.ρ]`; the **A0 bridge** `vanishingIdeal k Z = ker μ*` as a hypothesis — the
>   model-specific orbit↔kernel input (the abstract carrier never asserts `Z` or the orbit exists).
> - **Cited.** none new (same Phase-1 fact; `Ideal.quotientKerEquivRange` is Mathlib's first-iso).
> - **Deferred.** none.
> - **Status.** sorry-free.

## DLN re-derivation (consumer collapse)

> **Claim.** The DLN A4.1 lemma `ringKrullDim_range_orbitPullback_unbotD_eq_trdeg_toNat` is the orbit
> specialisation of the abstract anchor — the old standalone reindex+transport proof is **collapsed**.
>
> - **Lean:** `DLNFibre.Core.ringKrullDim_range_orbitPullback_unbotD_eq_trdeg_toNat`
>   (`lean/DLNFibre/Core/AffineNoetherRank.lean` @ `<commit-sha>`) — **signature unchanged**, body
>   re-derived (4 lines).
> - **Gloss.** `(M : Tuple d) ⊢ (ringKrullDim (orbitPullback M).range).unbotD 0 =`
>   `(Algebra.trdeg k (orbitPullback M).range).toNat`.
> - **Proved.** Apply the anchor at `dlnOrbit M` (`Core/OrbitVariety.lean`); `(dlnOrbit M).ρ = RepCoord d`
>   is `Finite`; `(dlnOrbit M).pullback = orbitPullback M` definitionally (`dlnOrbit_pullback`), so a
>   single `rwa [dlnOrbit_pullback]` finishes. The duplication (the old `renameEquiv` / `quotientEquivAlg`
>   transport) is removed.
> - **Consumers.** `OrbitImageDim.lean` consumes this DLN lemma; signature unchanged ⟹ green
>   (full aggregator build 3825 jobs, verified).
> - **Status.** sorry-free.

---

## Files

- NEW `lean/DLNFibre/Core/AlgebraicGeometry/Group/Orbit/Dimension.lean` — the abstract anchor (both
  forms) + the `finiteType_pullback_range` instance. Bare Mathlib-mirror namespace
  `AlgebraicGeometry.Group.Orbit` (L7). Wired into the aggregator transitively via `AffineNoetherRank`.
- EDIT `lean/DLNFibre/Core/AffineNoetherRank.lean` — import the anchor; collapse the DLN proof body to
  the re-derivation; docstring updated. Signature unchanged.

## Gates

- Full aggregator build `scripts/lb DLNFibre` — green, 3825 jobs.
- `scripts/sorries` — 0 sorry / 0 axiom / 0 native_decide / 0 #exit.
- `#print axioms` on both abstract forms + the re-derived DLN lemma = `[propext, Classical.choice,
  Quot.sound]`.

## Signature concern feeding P2.4/P2.5 (flag, do not act)

`[Finite G.ρ]` enters the carrier *here* (the dimension layer), not on the base carrier. P2.4/P2.5
add the deformation data `(C0, C1, δ)` and the geometric hypotheses (H1)/(H2); when those rungs need
`G.ρ` finite (e.g. for finite-dim cotangent / the δ-rank bound), they should carry `[Finite G.ρ]`
as a hypothesis on the relevant lemmas the same way — NOT retrofit it onto the base `AffineGVariety`.
