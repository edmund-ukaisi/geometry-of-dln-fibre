# Statement card — P1-R3: affine-domain no-drop dimension lemmas re-home

**Thread:** `03-affine-no-drop` (foundation-lift Phase 1, rung R3).
**Branch / commit:** `expedition/foundation-lift-p1` (off `origin/dev` `00fb7238` / PR #14), commit
`16cd40f2`. Pushed to `origin`.
**Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`,
not relied on the build's exit status). Full aggregator green (3819 jobs). Awaiting fidelity review.

## What moved (verbatim re-home, no hypothesis or proof change)

The four `[Field k]`-general trdeg-sandwich no-drop lemmas moved **out of** the now-deleted
`DLNFibre.Core.AffineLocalizationNoDrop` (namespace `DLNFibre.Core`) **into**
`lean/DLNFibre/Core/Dimension/Localization.lean` (namespace `DLNFibre.Core.Dimension`), beside R2's
always-true `≤`-half `ringKrullDim_localization_le`. The `≤`-half and the `≥`-half no-drop now share one
brick.

- **Namespace change:** `DLNFibre.Core` → `DLNFibre.Core.Dimension`. (The lemmas were previously
  reachable unqualified from `DLNFibre.Core`-namespace consumers; they now resolve via `open Dimension`
  — see re-pointing below.)
- **Proofs / signatures / hypotheses: byte-identical** to the source. This is a pure re-home (plus a
  merged Mathlib-grade module docstring covering both halves). No generalization beyond what was already
  there; no `[Field k]` loosening was available (the route is `dim = trdeg` via Noether normalization,
  which needs a field base).
- **Mathlib mirror:** `Mathlib.RingTheory.KrullDimension.Localization` — no such file upstream at this
  pin; co-located with R2 in the project's `Dimension/Localization.lean` so an upstream move is a
  file-move with no namespace surgery.
- **`@[stacks ...]`:** none attached (R2's precedent; no exact-match standalone tag — the trdeg-sandwich
  no-drop is not a single numbered Stacks statement).
- **Imports added to the target** (union with R2's): `DLNFibre.Core.AffineNoetherRank`,
  `DLNFibre.Core.Dimension.Integral`, `DLNFibre.Core.Dimension.Basic`, and the Mathlib localization set
  (`Localization.Away.Basic`, `Localization.Away.AdjoinRoot`, `Localization.FractionRing`,
  `Localization.LocalizationLocalization`, `Localization.Integral`). No import cycle (none of the three
  DLNFibre imports reaches `Dimension.Localization`). `Core`-only.

### The four lemmas (final, build-confirmed signatures)

```
theorem DLNFibre.Core.Dimension.ringKrullDim_eq_trdeg_of_fg_domain
    {k : Type u} [Field k] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ringKrullDim A = ((Algebra.trdeg k A).toNat : WithBot ℕ∞)

theorem DLNFibre.Core.Dimension.trdeg_localization_eq
    {k : Type u} [Field k] (D : Type u) [CommRing D] [IsDomain D] [Algebra k D]
    (M : Submonoid D) (hM : M ≤ nonZeroDivisors D)
    (S : Type u) [CommRing S] [Algebra k S] [Algebra D S] [IsScalarTower k D S]
    [IsLocalization M S] :
    Algebra.trdeg k S = Algebra.trdeg k D

theorem DLNFibre.Core.Dimension.ringKrullDim_localizationAway_eq_of_fg_domain
    {k : Type u} [Field k] (D : Type u) [CommRing D] [IsDomain D]
    [Algebra k D] [Algebra.FiniteType k D] (g : D) (hg : g ≠ 0) :
    ringKrullDim (Localization.Away g) = ringKrullDim D

theorem DLNFibre.Core.Dimension.ringKrullDim_localizationAway_eq_of_avoids_top_prime
    {k : Type u} [Field k] (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra k R] [Algebra.FiniteType k R] (g : R) (p₀ : Ideal R)
    [p₀.IsPrime] (htop : ringKrullDim (R ⧸ p₀) = ringKrullDim R) (hg : g ∉ p₀) :
    ringKrullDim (Localization.Away g) = ringKrullDim R
```

**Gloss.**
- `ringKrullDim_eq_trdeg_of_fg_domain` — for a finitely-generated `k`-domain `A`, the Krull dimension
  equals the transcendence degree over `k` (`dim = trdeg`).
- `trdeg_localization_eq` — for a `k`-domain `D` and a `k`-algebra localization `S = M⁻¹D` at a
  submonoid `M` of non-zero-divisors, `trdeg k S = trdeg k D` (the localization sits between `D` and
  `Frac D`, so the relative `trdeg` is `0`).
- `ringKrullDim_localizationAway_eq_of_fg_domain` — for an f.g. `k`-domain `D` and `g ≠ 0`, inverting
  `g` does not change the dimension: `dim (D[1/g]) = dim D`.
- `ringKrullDim_localizationAway_eq_of_avoids_top_prime` — for an f.g. `k`-algebra `R` (possibly
  reducible, Noetherian) and `g : R` avoiding a *top-dimensional* prime `p₀`
  (`dim (R ⧸ p₀) = dim R`, `g ∉ p₀`), inverting `g` preserves the dimension: `dim (R[1/g]) = dim R`.
  (Minimality of `p₀` is not used — it need only be a prime carrying the full dimension.)

- **Proved.** All four, unconditionally, sorry-free, axiom-clean `[propext, Classical.choice,
  Quot.sound]` (forced via `lake env lean` `#print axioms`).
- **Assumed.** Only the named hypotheses above (`[Field k]`, fg-domain / fg-Noetherian-algebra, the
  nonzero / avoidance witnesses). Minimal — confirmed by the build; not loosened or tightened in the
  re-home.
- **Cited.** none (pure commutative algebra over Mathlib + the #14 `Dimension`/`AffineNoetherRank`
  helpers).
- **Deferred.** none.

## Sibling-clash gate (lean/CLAUDE.md) — CLEARED

`rg` of all four names across `DLNFibre/Core/Dimension/` (the siblings `AffineDomain, Basic, Catenary,
Codimension, Integral, Localization, Regular, Smooth`): no pre-existing definition of any of the four.
Globally, the four names were defined **only** in the deleted `AffineLocalizationNoDrop.lean`; after the
move they are defined only in `Dimension/Localization.lean`. Full aggregator builds green
(`environment already contains` would fire on a clash — it did not).

## Re-pointing (L2 transitive-consumer sweep done)

Every consumer of the moved identifiers re-pointed; full-aggregator build is the authoritative gate
(transitive/unqualified consumers break only there). The five consumers:

| File | Use | Edit |
|------|-----|------|
| `Core/SchurSideNoDrop.lean` | **code** (`..._avoids_top_prime`, line 90) | import → `Dimension.Localization`; `open ... Dimension` |
| `Core/SourceNoDrop.lean` | **code** (`..._avoids_top_prime`, line 235); reached the lemma *transitively* via `ChartLocalizedCoordinates → SchurSideNoDrop` | `open ... Dimension` added; docstring ref re-qualified |
| `Core/TopDimMinPrimesW1W2.lean` | **code** (`..._of_fg_domain`, line 79) | import → `Dimension.Localization`; `open ... Dimension` |
| `Core/ChartLocalizedPolyDim.lean` | docstring only (no code use) | import → `Dimension.Localization` |
| `Core/TopDimMinPrimesLocalization.lean` | docstring only (already imports `Dimension.Localization`, already `open ... Dimension`) | docstring ref re-qualified to `Core.Dimension.` |

`DLNFibre.lean` aggregator: the `import DLNFibre.Core.AffineLocalizationNoDrop` line removed (the file is
deleted; the content is now imported transitively via `Dimension.Localization`, which the aggregator
already imports from R2). `AffineLocalizationNoDrop.lean` **deleted** (`git rm`) — it held only these
four lemmas, so it was empty after the move.

## Per-prime no-drop flag for R5 (REQUESTED)

The `hper` input that `TopDimMinPrimesLocalization`'s keystone `topDimMinPrimes_ncard_away_eq` consumes
is **NOT one of these four lemmas** — it is a **hypothesis** of the keystone, of shape

    hper : ∀ p ∈ TopDimMinPrimes A,
      ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) = ringKrullDim (A ⧸ p)

i.e. a **per-prime / componentwise** no-drop. Its discharge lives **downstream**, in
`Core/TopDimMinPrimesW1W2.lean`:

> `topDimMinPrimes_ncard_away_eq_of_fgDomain` (line 67) — the abstract away-survival wrapper that feeds
> the keystone the `hper` by proving it *for each top prime* `p`: `A ⧸ p` is an f.g. `k`-domain and
> `mk p f ≠ 0` (from avoidance), so `ringKrullDim_localizationAway_eq_of_fg_domain (k := k) (A ⧸ p)
> (mk p f) hgne` (line 79) gives the equality.

So R5's chain for the count survival is: `topDimMinPrimes_ncard_away_eq` (keystone, takes `hper`) ←
`topDimMinPrimes_ncard_away_eq_of_fgDomain` (discharges `hper` per prime) ←
`ringKrullDim_localizationAway_eq_of_fg_domain` (this rung, R3). When R5 extracts the
`TopDimMinPrimes{Localization,…}` transport, it must carry the **per-prime** shape: the `hper` is invoked
once per top prime and does **NOT** fold out of a global no-drop + avoidance. The obstruction is the
**DVR-at-a-uniformizer**: a domain localized at a non-unit can drop dimension, so "globally inverting `f`
preserves `dim A`" plus "`f` avoids the top primes" does not by itself give the per-component equality —
each `A ⧸ p` must be an f.g. `k`-domain with `f̄ ≠ 0` and the no-drop applied to it individually. (This
matches the reviewer + Codex + memory record; the R3 re-home preserved it intact.)

## Holes / surprises

- **Job count dropped 3820 → 3819.** Expected: one module (`AffineLocalizationNoDrop`) was deleted while
  its content folded into `Dimension/Localization`, which the consumers already reach transitively. Not a
  regression.
- **`SourceNoDrop` reached the lemma only transitively** (no direct import of `AffineLocalizationNoDrop`),
  via `ChartLocalizedCoordinates → SchurSideNoDrop → AffineLocalizationNoDrop`. This is exactly the L2
  trap: it had no direct import to re-point, only an `open Dimension` to add — caught by the full-aggregator
  build, not by a closure-only build of any single edited module.
- **Pre-existing `longLine` warnings** in `TopDimMinPrimesW1W2.lean` (docstring lines, untouched by me) and
  `DLNFibre.lean:475` (R2's comment). My new module `Dimension/Localization.lean` builds with **zero**
  longLine warnings (L4 codepoint reflow done on the docstrings I added). I did not reflow pre-existing
  docstrings outside the moved content (out of scope for a re-home rung).
