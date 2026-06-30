# Statement card — P1-R2: localization `≤`-half re-home

**Thread:** `02-localization-le` (foundation-lift Phase 1, rung R2).
**Branch / commit:** `expedition/foundation-lift-p1` (off `origin/dev` `00fb7238` / PR #14, via the P1-R1 doc commit `0dc4d84e`). Pushed to `origin`.

## New module

- **Path:** `lean/DLNFibre/Core/Dimension/Localization.lean`
- **Namespace:** `DLNFibre.Core.Dimension` (top-level lemma — no extra namespace; Mathlib's
  `KrullDimension/*` lemmas are unnamespaced, so this matches).
- **Mathlib mirror:** `Mathlib.RingTheory.KrullDimension.Localization` — **no such file exists upstream**
  at this pin (`RingTheory/KrullDimension/` has `{Basic, Field, LocalRing, Module, NonZeroDivisors,
  PID, Polynomial, Regular, Zero}`, no `Localization`), and there is **no `ringKrullDim_localization*`
  anywhere in Mathlib (0 hits)` — so this is a genuine gap and an upstream move would be a fresh file.
- **Placement choice:** `Core/Dimension/Localization.lean` (the existing #14 `Core/Dimension/*` family,
  namespace `DLNFibre.Core.Dimension`), **not** a new `Core/KrullDimension/`. Justification: #14 already
  established `Core/Dimension/{Basic,Integral,Catenary,AffineDomain,Codimension,Smooth,Regular}` as the
  project's Krull-dimension home with namespace `DLNFibre.Core.Dimension`; P1-R3 (the `≥`-half no-drop,
  pending) targets the same `Core/.../Localization` module, so co-locating R2 and R3 in
  `Dimension/Localization.lean` keeps one Krull-dimension family and minimises the eventual upstream
  surgery. (The two Mathlib homes `KrullDimension.Localization` vs `Dimension.*` differ only by upstream
  naming taste; the project-local family is already `Dimension`.)
- **Imports:** `Mathlib.RingTheory.Localization.Ideal`, `Mathlib.RingTheory.KrullDimension.Basic`,
  `Mathlib.RingTheory.Spectrum.Prime.Topology`. `Core`-only (no `DLNFibre.DLN`).

## The re-homed lemma (final, build-confirmed)

```
theorem DLNFibre.Core.Dimension.ringKrullDim_localization_le
    {R : Type u} [CommRing R] (M : Submonoid R) (S : Type u) [CommRing S] [Algebra R S]
    [IsLocalization M S] :
    ringKrullDim S ≤ ringKrullDim R
```

**Localization does not increase Krull dimension.** For any localization `S = M⁻¹R`,
`ringKrullDim S ≤ ringKrullDim R`.

- **Hypotheses (minimal, build-confirmed):** `[CommRing R]`, `M : Submonoid R`, and the localization
  triple `[CommRing S] [Algebra R S] [IsLocalization M S]`. `R` and `S` share the universe `u` — the
  same-universe constraint already present in the source (`Order.krullDim_le_of_strictMono` is
  universe-polymorphic, but `PrimeSpectrum.comap (algebraMap R S)` between the two spectra is cleanest
  same-universe; this was not loosened — kept as-is, matching the original SPIKE, since both DLN call
  sites instantiate at one universe).
- **Already general:** the lemma was already at full generality in the source (`LocalizationKrullDim`);
  this rung is **pure re-home + Mathlib-grade docstring/placement**, no hypothesis change and no proof
  change (the four-line proof is byte-identical).
- **Name = content:** `ringKrullDim_localization_le` = "the Krull dimension of a localization is `≤`".
  No overclaim — this is the always-true `≤` half; the genuine *no-drop* `≥` (P1-R3) is a separate
  downstream lemma, named in the docstring as *not* part of this file.
- **Proof:** `PrimeSpectrum.comap (algebraMap R S)` is monotone (`Ideal.comap_mono`) and injective
  (`PrimeSpectrum.localization_comap_injective`), hence strict-monotone
  (`Monotone.strictMono_of_injective`); `Order.krullDim_le_of_strictMono` then gives the inequality.
- **`@[stacks ...]`:** **none attached, deliberately.** The Stacks Project carries this fact only
  through the prime-bijection of a localization (tag `00KD` defines dimension/height; tag `00OQ` is a
  different statement — regularity of polynomial algebras), not as a standalone numbered dimension
  inequality. Attaching a `@[stacks ...]` would overstate the match; the docstring records the
  conceptual basis (order-injection of spectra) instead. (#14's `Dimension/*` files tag only where the
  match is exact, e.g. `@[stacks 00OS]`/`00OJ`/`00GU`/`00OK`.)

## Sibling-clash check (lean/CLAUDE.md gate) — CLEARED

- `rg ringKrullDim_localization_le` over all of Mathlib: **0 hits** (no clash, genuine gap).
- `rg` over `DLNFibre/`: the name now lives in `Dimension/Localization.lean` (def + docstring +
  non-vacuity `example`) plus the two qualified-by-`open`-`Dimension` call sites
  (`TopDimMinPrimesLocalization`, `AffineLocalizationNoDrop`). No stale duplicate.
- No other top-level name introduced; the new file shares the `Dimension` namespace with the #14
  family and adds no constant that collides with a sibling.

## Re-pointed consumers

- `lean/DLNFibre/Core/TopDimMinPrimesLocalization.lean`:
  - Import swapped `DLNFibre.Core.LocalizationKrullDim` → `DLNFibre.Core.Dimension.Localization`.
  - `open IsLocalization Localization` → `open IsLocalization Localization Dimension` (so the
    unqualified `ringKrullDim_localization_le` at line ~139, inside `namespace DLNFibre.Core`, still
    resolves). Content unchanged.
- `lean/DLNFibre/Core/AffineLocalizationNoDrop.lean`:
  - Import swapped `DLNFibre.Core.LocalizationKrullDim` → `DLNFibre.Core.Dimension.Localization`.
  - **No `open` change needed** — it already does `open Algebra Dimension`, so the unqualified call at
    line ~143 resolves through the moved namespace. Content unchanged.
- `lean/DLNFibre.lean` (single-writer aggregator):
  - **Removed** the old `import DLNFibre.Core.LocalizationKrullDim` (+ its comment).
  - **Added** `import DLNFibre.Core.Dimension.Localization` at the end (P1-R2 comment block), mirroring
    the P1-R1 end-of-file placement.
- **`LocalizationKrullDim.lean` was DELETED** (`git rm`): it held only the moved lemma + its docstring +
  the non-vacuity `example` (all carried over to the new file), so it was left empty of substantive
  content. No remaining content to retain.

## L2 (transitive-consumer sweep) — done

`rg ringKrullDim_localization_le` across all `DLNFibre/`: only the def in `Dimension/Localization.lean`
+ the two call sites + the aggregator comment. **Full aggregator build** (not just the touched modules)
run to catch unqualified/transitive consumers — green at the unchanged 3820 jobs (net-neutral re-home).

## Gate status

- **Build:** `./scripts/lb DLNFibre` (full aggregator) **green — 3820 jobs** (same job count as the
  pre-move baseline — a re-home, not new content). The new module is `longLine`-clean (the one initial
  `:35:100` docstring overflow was reflowed per L4). Pre-existing `longLine` warnings in untouched files
  (`FibreTargetOverlap`, `AffineLocalizationNoDrop:59`) only.
- **Sorries:** `scripts/sorries` = **0 sorry, 0 #exit, 0 native_decide, 0 axiom**.
- **Axioms:** force-elaborated `#print axioms DLNFibre.Core.Dimension.ringKrullDim_localization_le` =
  **`[propext, Classical.choice, Quot.sound]`** (clean).

## Holes / surprises

- No holes. Pure re-home of an already-general lemma; no proof or hypothesis change.
- **One taste call recorded:** declined to attach a `@[stacks ...]` tag (no exact Stacks match — the
  fact is a corollary of the prime-bijection, not a standalone numbered tag); the honest choice over a
  near-miss tag, consistent with #14's exact-match-only tagging.
