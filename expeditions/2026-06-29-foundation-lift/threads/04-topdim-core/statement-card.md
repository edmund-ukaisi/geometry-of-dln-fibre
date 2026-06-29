# Statement card — P1-R4: `TopDimMinPrimes` count-engine core

**Rung:** foundation-lift P1-R4 (the low-risk, high-reuse warm-up — generalise-and-re-home an
already-green core). **Branch:** `expedition/foundation-lift-p1`. **Commit:** `9a922438` (Lean
re-home) — this card added in the follow-up commit on the same branch.

**New module:** `lean/DLNFibre/Core/MinimalPrime/TopDimensional.lean`
**Namespace:** `Ideal` — mirrors the Mathlib home `Mathlib.RingTheory.Ideal.MinimalPrime` (a plausible
`…/MinimalPrime/TopDimensional.lean`), exactly as the sibling `Core/MinimalPrime/Finite.lean` (R1).
**Source (DELETED):** `lean/DLNFibre/Core/TopDimMinPrimes.lean` (namespace `DLNFibre.Core`).

This is a **verbatim re-home**: all six declarations are byte-identical in statement and proof term to
the audited source; the only diffs are the namespace (`DLNFibre.Core` → `Ideal`), the import header,
and one cleaned docstring parenthetical. Git detected it as a rename. Fidelity reviewer verdict: **PASS**.

---

## The declarations (exact names / signatures / minimal hypotheses — build-confirmed)

Module-wide: `variable {A : Type*} [CommRing A] {B : Type*} [CommRing B]`. **Minimal hypotheses are
`[CommRing A]` (+ `[CommRing B]` for the transport lemmas) — nothing stronger.** No `Noetherian`,
no `Field`, no `Finite`/`Fintype`, no `IsDomain` anywhere in the module (grep-confirmed by the
reviewer). `[CommRing]` is the natural minimal home for `ringKrullDim`; not weakenable to `CommSemiring`
without losing the `comap_bot_of_injective`/quotient transport machinery.

> **Def.** `Ideal.TopDimMinPrimes (A : Type*) [CommRing A] : Set (Ideal A)`
>   `:= {p | p ∈ minimalPrimes A ∧ ringKrullDim (A ⧸ p) = ringKrullDim A}`
> - **Gloss.** The minimal primes `p` of `A` whose quotient `A ⧸ p` realises the full Krull dimension
>   `ringKrullDim A` — the irreducible components of `Spec A` of maximal dimension (minimal codimension).
> - **Proved.** It is exactly this set (definitional); `mem_topDimMinPrimes` is the `Iff.rfl` membership
>   unfolding; `isPrime_of_mem_topDimMinPrimes` extracts `p.IsPrime` from `minimalPrimes` membership.

> **Theorem.** `Ideal.comap_mem_topDimMinPrimes (e : A ≃+* B) {p : Ideal B}`
>   `(hp : p ∈ TopDimMinPrimes B) : p.comap (e : A →+* B) ∈ TopDimMinPrimes A`
> - **Gloss.** `comap` along a ring iso sends a top-dim minimal prime of `B` to one of `A`. Minimal-prime
>   membership transports via `Ideal.comap_minimalPrimes_eq_of_surjective` + `comap_bot_of_injective`;
>   the Krull-dim equality via `A ⧸ p.comap e ≃+* B ⧸ p` (`Ideal.quotientEquiv`) and
>   `ringKrullDim A = ringKrullDim B`.

> **Theorem.** `Ideal.bijOn_comap_topDimMinPrimes (e : A ≃+* B) :`
>   `Set.BijOn (Ideal.comap (e : A →+* B)) (TopDimMinPrimes B) (TopDimMinPrimes A)`
> - **Gloss.** `comap e` restricts to a bijection `TopDimMinPrimes B ≃ TopDimMinPrimes A`; the two-sided
>   inverse is `comap e.symm` (injectivity from surjectivity of `e`, surjectivity via `comap_map_of_bijective`).

> **Theorem.** `Ideal.topDimMinPrimes_ncard_eq_of_ringEquiv (e : A ≃+* B) :`
>   `(TopDimMinPrimes A).ncard = (TopDimMinPrimes B).ncard`
> - **Gloss.** The top-dimensional minimal-prime **count** is a ring-isomorphism invariant.
> - **Proved.** Unconditional from `(bijOn_comap_topDimMinPrimes e).ncard_eq` — `Set.ncard`, so the
>   equality holds even for infinite sets (no hidden finiteness). The name "ring-isomorphism invariant"
>   is exactly the content.
> - **Cited / Deferred.** None.

---

## Sibling-clash gate (cleared)

- **Mathlib v4.29:** `rg` over the resolved store finds **zero** hits for `TopDimMinPrimes`,
  `topDimMinPrimes`, or `bijOn_comap` (stems). No upstream collision.
- **`Ideal`-namespace siblings:** disjoint from `Core/MinimalPrime/Finite.lean` (R1's
  `minimalPrimes_sInf_of_finite_of_isPrime`) — no shared names.

## What re-pointed (L2 transitive-consumer sweep)

16 consumer files reference the moved symbols in code; each gained a selective
`open Ideal (TopDimMinPrimes mem_topDimMinPrimes isPrime_of_mem_topDimMinPrimes`
`comap_mem_topDimMinPrimes bijOn_comap_topDimMinPrimes topDimMinPrimes_ncard_eq_of_ringEquiv)`
after its `namespace DLNFibre.Core` line — exactly the 6 names, so **no `Ideal.map`/`Ideal.comap`
collision** (selective open was chosen precisely because `TopDimMinPrimesPoly`/`TopComponentsTopDim`
use bare `map`/`comap`/`height` heavily; a bare `open Ideal` would shadow).

- **5 direct importers** also swapped `import DLNFibre.Core.TopDimMinPrimes` →
  `import DLNFibre.Core.MinimalPrime.TopDimensional`: `FibreTopDimDetUnit`, `TopDimMinPrimesBridge`,
  `TopDimMinPrimesChartE`, `TopDimMinPrimesLocalization`, `TopDimMinPrimesPoly`.
- **11 transitive consumers** (no direct import — symbol arrives through an importer they already
  import) got only the selective open: `FibreComponentOrbit`, `FibreComponentOrbitTransport`,
  `FibreSmoothBlock`, `FibreSmoothBlockExists`, `FibreThetaCount`, `FibreThetaCountArbitrary`,
  `TopComponentsTopDim`, `TopDimMinPrimesRadical`, `TopDimMinPrimesW0`, `TopDimMinPrimesW1W2`,
  `TopDimMinPrimesW2`.
- **Aggregator** `DLNFibre.lean`: removed the old `import …TopDimMinPrimes`, appended
  `import DLNFibre.Core.MinimalPrime.TopDimensional` with a P1-R4 comment block.

Every selective open is used (no unused-open warning in any edited file).

## Build / sorry / axiom status

- Full aggregator `./scripts/lb DLNFibre` **green — 3819 jobs**.
- `./scripts/sorries`: **0 sorry / 0 #exit / 0 native_decide / 0 axiom**.
- `#print axioms` (via full aggregator) on all 6 decls = **`[propext, Classical.choice, Quot.sound]`**.
- Old `DLNFibre.Core.TopDimMinPrimes` confirmed gone (`#check` errors "Unknown identifier").
- LoC delta: 18 files changed, +87 / −29 (the −105/−ish in `git diff --stat` reflects the rename).
- No new linter warnings introduced; the one remaining `DLNFibre.lean` longLine (line 475) is the
  pre-existing R2 comment, outside this change.

**Status.** sorry-free + reviewed (fidelity PASS).

---

## Note for P1-R5 (the transport rungs that stack on this core)

The R5 transport modules (`TopDimMinPrimes{Localization,Poly,Radical,Bridge}`) build their `ncard`
chains on `Ideal.topDimMinPrimes_ncard_eq_of_ringEquiv` and the membership/bijection lemmas above —
all now in `Core.MinimalPrime.TopDimensional` (ns `Ideal`). They reference these via the selective
`open Ideal (...)` already inserted, so R5 only needs to re-home its *own* content (the
localization/poly/radical/bridge transport lemmas) and keep that open line. The flagged R5 **crux**
(`TopDimMinPrimesLocalization`'s per-prime no-drop) is **not** in this core — this module carries only
the `RingEquiv` transport, which is unconditional and finiteness-free; the per-prime no-drop is a
separate, genuinely-harder input (DVR-at-uniformizer counterexample to the global-no-drop+avoidance
shortcut — see priorities P1-R5 + memory `per-prime-nodrop-localization`). Nothing in this core
constrains or eases that; R5's `hper` hypothesis (`∀ p ∈ TopDimMinPrimes A, ringKrullDim (Away (mk p f))
= ringKrullDim (A⧸p)`) is discharged downstream in `TopDimMinPrimesW1W2` via R3's
`ringKrullDim_localizationAway_eq_of_fg_domain`, not from this module.
