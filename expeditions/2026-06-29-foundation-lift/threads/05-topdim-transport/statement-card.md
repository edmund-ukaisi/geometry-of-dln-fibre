# Statement card — P1-R5 `TopDimMinPrimes` general count-transport rungs

**Thread:** 05-topdim-transport (foundation-lift Phase 1, the flagged CRUX rung)
**Branch:** `expedition/foundation-lift-p1`
**Build:** `./scripts/lb DLNFibre` green at **3819 jobs** (matches baseline). `scripts/sorries` clean
(0 sorry / 0 #exit / 0 native_decide / 0 axiom). All transport headlines axiom-clean
`[propext, Classical.choice, Quot.sound]`; the DLN downstream headline
`ncard_topDimMinPrimes_fibre_eq_cTheta_dminus` also re-verified `[propext, Classical.choice,
Quot.sound]` (payoff axioms unchanged).

## What was done

Re-homed the four general count-transport modules from `DLNFibre/Core/TopDimMinPrimes{Localization,
Poly,Radical,Bridge}.lean` into the `Core/MinimalPrime/` family, built on R4's
`Core/MinimalPrime/TopDimensional.lean`. All in namespace **`Ideal`** (mirrors
`Mathlib.RingTheory.Ideal.MinimalPrime`, matching R4) — so an upstream move is a file-move with no
namespace surgery. The four source modules are **deleted** (their entire content was general
transport). Two general lemmas that lived in DLN-coupled modules were pulled into the new clean
modules so the transport family imports only clean `Core` (see "namespace / clash decisions").

## New modules + headline signatures (all ns `Ideal`)

### `Core/MinimalPrime/Localization.lean` (226 LoC) — THE CRUX (away-localization survival)

```
theorem ringKrullDim_quotient_map_localizationAway_eq (f : A) (S : Type u) [CommRing S]
    [Algebra A S] [IsLocalization.Away f S] (p : Ideal A) :
    ringKrullDim (S ⧸ Ideal.map (algebraMap A S) p)
      = ringKrullDim (Localization.Away (Ideal.Quotient.mk p f))

theorem bijOn_comap_topDimMinPrimes_away (f : A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization.Away f S] (hdim : ringKrullDim S = ringKrullDim A)
    (havoid : ∀ p ∈ TopDimMinPrimes A, f ∉ p)
    (hper : ∀ p ∈ TopDimMinPrimes A,
      ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) = ringKrullDim (A ⧸ p)) :
    Set.BijOn (Ideal.comap (algebraMap A S)) (TopDimMinPrimes S) (TopDimMinPrimes A)

theorem topDimMinPrimes_ncard_away_eq (f : A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization.Away f S] (hdim : ringKrullDim S = ringKrullDim A)
    (havoid : ∀ p ∈ TopDimMinPrimes A, f ∉ p)
    (hper : ∀ p ∈ TopDimMinPrimes A,
      ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) = ringKrullDim (A ⧸ p)) :
    (TopDimMinPrimes S).ncard = (TopDimMinPrimes A).ncard
```
Helpers (all ns `Ideal`): `comap_mem_minimalPrimes_of_away`,
`disjoint_powers_of_mem_topDimMinPrimes`, `comap_mem_topDimMinPrimes_of_away`,
`map_comap_eq_of_mem_topDimMinPrimes`, `map_mem_minimalPrimes_of_avoid`,
`map_mem_topDimMinPrimes_of_avoid` (this last is the **only** lemma that consumes `hper`).
`[CommRing A]` + the `IsLocalization.Away f S` interface; `universe u`.

### THE `hper` HYPOTHESIS — verbatim as extracted (controller decorrelated-reviews exactly this)

```
hper : ∀ p ∈ TopDimMinPrimes A,
  ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) = ringKrullDim (A ⧸ p)
```

**Confirmed NOT weakened.** It is the genuine **per-prime** statement: universally quantified over
`p ∈ TopDimMinPrimes A`, with the localizing element taken as the image `Ideal.Quotient.mk p f` of
`f` **in that specific quotient `A ⧸ p`**, equated to `ringKrullDim (A ⧸ p)`. This is byte-identical
to the hypothesis in the original `TopDimMinPrimesLocalization` source (the same `∀ p ∈ … , …` form).

It is **separate** from the global `hdim : ringKrullDim S = ringKrullDim A` argument, and is NOT
derivable from `hdim + havoid`. The non-foldability: a domain localized at a *non-unit* can drop
Krull dimension — the **DVR-at-a-uniformizer** counterexample (a 1-dim DVR `A`, `f` a uniformizer:
`Localization.Away f` is the fraction field, dimension 0; yet the global `ringKrullDim S =
ringKrullDim A` survival statement plus avoidance of the top primes does not see this per-component
drop). So `hper` must be **invoked once per surviving top prime** — it cannot be folded out of a
global no-drop + avoidance. (Reviewer + Codex + memory `per-prime-nodrop-localization.md` recorded
this previously.) In the DLN applications it is discharged once-per-top-prime in
`TopDimMinPrimesW1W2` via R3's `Core.Dimension.ringKrullDim_localizationAway_eq_of_fg_domain` (each
`A ⧸ p` an f.g. `k`-domain, `f̄ ≠ 0`) — the discharge stayed local, exactly as the priorities flag
required.

### `Core/MinimalPrime/Polynomial.lean` (210 LoC) — MvPolynomial-extension descent

```
theorem topDimMinPrimes_mvPolynomial_ncard_eq [IsNoetherianRing A] [Finite ι] :
    (TopDimMinPrimes (MvPolynomial ι A)).ncard = (TopDimMinPrimes A).ncard
```
Plus `bijOn_comap_C_topDimMinPrimes`, `map_C_mem_topDimMinPrimes`, `comap_C_mem_topDimMinPrimes`,
`ringKrullDim_quotient_map_C`, `map_comap_C_of_mem_minimalPrimes`, `comap_C_mem_minimalPrimes`,
`map_C_mem_minimalPrimes`, `comap_map_C_eq`, and the **re-homed** prime-lift
`isPrime_map_mvPolynomial_C` (was `isPrime_map_C_of_isPrime` in `SchurSideNoDrop`; renamed — see
clash note).

### `Core/MinimalPrime/Radical.lean` (127 LoC) — radical-insensitivity

```
theorem topDimMinPrimes_quotient_radical_ncard_eq (J : Ideal R) :
    (TopDimMinPrimes (R ⧸ J)).ncard = (TopDimMinPrimes (R ⧸ J.radical)).ncard

theorem topDimMinPrimes_quotient_ncard_eq_of_minimalPrimes_eq (I J : Ideal R)
    (hmin : I.minimalPrimes = J.minimalPrimes)
    (hdim : ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ J)) :
    (TopDimMinPrimes (R ⧸ I)).ncard = (TopDimMinPrimes (R ⧸ J)).ncard
```
Plus `def quotTopDimSet`, `bijOn_comap_quotTopDimSet`, `ncard_topDimMinPrimes_quotient_eq`, and the
**re-homed** general third-iso-theorem dimension fact `ringKrullDim_doubleQuot_eq` (was in DLN-coupled
`TopComponentsTopDim`; `[CommRing R]`, any ideal `I`, any prime `P` of `R ⧸ I`).

### `Core/MinimalPrime/Bridge.lean` (113 LoC) — height ↔ dimension biconditional

```
theorem ringKrullDim_quotient_eq_iff_height_eq (I : Ideal (MvPolynomial σ k)) (hIne : I ≠ ⊤)
    {p : Ideal (MvPolynomial σ k)} (hp : p ∈ I.minimalPrimes) :
    ringKrullDim (MvPolynomial σ k ⧸ p) = ringKrullDim (MvPolynomial σ k ⧸ I)
      ↔ p.height = I.height
```
Plus `ringKrullDim_quotient_prime_eq`, `ringKrullDim_quotient_eq_of_ne_top`, `height_prime_le_card`,
`height_prime_ne_top` (`[Field k] [Finite σ]`). Now imports the clean `Core.Dimension.Codimension`
(#14) for the catenary facts, instead of the DLN-coupled `RadicalCatenary`.

## Namespace / sibling-clash decisions

- **All four modules → ns `Ideal`** (matches R4 `TopDimensional`). Headline names clash-free against
  Mathlib + the `MinimalPrime/` neighbours (`Finite`, `TopDimensional`) — `rg` gate cleared.
- **`isPrime_map_C_of_isPrime` renamed → `isPrime_map_mvPolynomial_C`.** Mathlib already has
  `Ideal.isPrime_map_C_of_isPrime` (the *univariate* `R[X]` version, an `instance`); ours is the
  *multivariate* `MvPolynomial`. Putting the unchanged name in ns `Ideal` would clash; name = content
  demands the distinct multivariate name. Re-pointed its one consumer (`SchurSideNoDrop`) +
  re-homed the def out of DLN-coupled `SchurSideNoDrop`.
- **`ringKrullDim_doubleQuot_eq` re-homed** from DLN-coupled `TopComponentsTopDim` into
  `MinimalPrime/Radical` (general `[CommRing R]`, no clash) so Radical imports only clean `Core`.

## What was re-pointed (L2 transitive-consumer sweep + full-build)

The brief named the 5 DLN keystones; the full sweep found these consumers of the moved identifiers
(import swap and/or `open Ideal (…)` extension):

- **`TopDimMinPrimesW1W2`** — imports → `MinimalPrime.{Localization,Polynomial,Radical}`; `open Ideal`
  += `topDimMinPrimes_ncard_away_eq comap_C_mem_minimalPrimes map_comap_C_of_mem_minimalPrimes
  quotTopDimSet bijOn_comap_quotTopDimSet`.
- **`TopDimMinPrimesW0`** — import `TopDimMinPrimesRadical` → `MinimalPrime.Radical` +
  `TopComponentsTopDim` (it used `height_sigmaIdeal_eq_cCodim` only transitively before); `open Ideal`
  += `quotTopDimSet bijOn_comap_quotTopDimSet ncard_topDimMinPrimes_quotient_eq
  ringKrullDim_quotient_eq_iff_height_eq`.
- **`TopComponentsTopDim`** (DLN wire) — import `TopDimMinPrimesBridge` → `MinimalPrime.Bridge` +
  `MinimalPrime.Radical` + **added `RadicalCatenary`** (it used `vanishingIdeal_ne_top_of_nonempty`
  via the old Bridge→RadicalCatenary chain); deleted its local `ringKrullDim_doubleQuot_eq` def;
  `open Ideal` += `ringKrullDim_doubleQuot_eq ringKrullDim_quotient_eq_iff_height_eq`.
- **`SchurSideNoDrop`** — import += `MinimalPrime.Polynomial`; deleted local `isPrime_map_C_of_isPrime`;
  one usage → `Ideal.isPrime_map_mvPolynomial_C`.
- **`FibreThetaCount`** — imports `TopDimMinPrimes{Poly,Radical}` → `MinimalPrime.{Polynomial,Radical}`;
  `open Ideal` += `topDimMinPrimes_mvPolynomial_ncard_eq topDimMinPrimes_quotient_radical_ncard_eq`.
- **`FibreThetaCountArbitrary`** — `open Ideal` += `topDimMinPrimes_quotient_radical_ncard_eq` (import
  via `FibreThetaCount`).
- **`FibreComponentOrbit`** — `open Ideal` += `quotTopDimSet bijOn_comap_quotTopDimSet` (import via
  `TopDimMinPrimesW0`).
- **`TopDimMinPrimesGfibAvoid`, `FibreComponentOrbitIso`** — docstring-only references to old module
  names, updated; no code/import change.
- **`DLNFibre.lean`** aggregator — removed the 4 stale `TopDimMinPrimes{Localization,Poly,Radical,
  Bridge}` imports; appended the 4 new `MinimalPrime.{Localization,Polynomial,Radical,Bridge}` imports
  after `MinimalPrime.TopDimensional` (with a P1-R5 comment block).
- **`TopDimMinPrimesW2`, `TopDimMinPrimesChartE`** — named keystones but reference no moved identifier
  (W2 imports W1W2; ChartE imports `MinimalPrime.TopDimensional`); no change needed.

## Files

New (ns `Ideal`, all `Core`-only):
- `lean/DLNFibre/Core/MinimalPrime/Localization.lean`
- `lean/DLNFibre/Core/MinimalPrime/Polynomial.lean`
- `lean/DLNFibre/Core/MinimalPrime/Radical.lean`
- `lean/DLNFibre/Core/MinimalPrime/Bridge.lean`

Deleted: `lean/DLNFibre/Core/TopDimMinPrimes{Localization,Poly,Radical,Bridge}.lean`.

## LoC delta
+676 (4 new modules) − 638 (4 deleted source modules) − ~22 (re-homed defs removed from
`TopComponentsTopDim` + `SchurSideNoDrop`) + edits to 8 consumers + aggregator. Net ≈ +16 source
lines, mostly upgraded docstrings; no proof-term growth (the proofs are verbatim re-homes).

## Honesty / uncertainty flags

- **`hper` shape — fully certain.** Verbatim per-prime, byte-identical to the source; not weakened
  to a global form; `hdim` is the separate global input. The non-foldability (DVR-at-uniformizer) is
  documented in the module header and not silently discharged. This is the rung's CRUX and warrants
  the decorrelated review on exactly the `topDimMinPrimes_ncard_away_eq` signature above.
- **One non-obvious re-pointing surprise:** `TopComponentsTopDim` needed `RadicalCatenary` added
  explicitly — it consumed `vanishingIdeal_ne_top_of_nonempty` only through the now-broken
  `Bridge → RadicalCatenary` transitive chain. Caught by the L2 full-build; `TopComponentsTopDim` is
  itself DLN-coupled, so importing `RadicalCatenary` there is in-scope (no clean-Core regression).
- No holes; all proofs are direct re-homes with only namespace/`open` adjustments.
