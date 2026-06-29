# Statement card — P1-R1: minimal primes of a finite-prime `sInf` SPIKE

**Thread:** `01-minimalprimes-spike` (foundation-lift Phase 1, rung R1 — warm-up).
**Branch / commit:** `expedition/foundation-lift-p1` @ `5e0ea019` (off scaffold `8c4c1650` = `origin/dev` `00fb7238` / PR #14). Pushed to `origin`.

## New module

- **Path:** `lean/DLNFibre/Core/MinimalPrime/Finite.lean`
- **Namespace:** `Ideal`
- **Mathlib mirror:** `Mathlib.RingTheory.Ideal.MinimalPrime` (the new file sits as a plausible `…/MinimalPrime/Finite.lean`; Mathlib's dir currently has `Basic.lean`, `Colon.lean`, `Localization.lean`, `Noetherian.lean` — no `Finite.lean`, so an upstream move is a file-move with no namespace surgery).
- **Imports:** `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`, `Mathlib.RingTheory.Ideal.Operations`. `Core`-only (no `DLNFibre.DLN`).

## The extracted lemma (final, build-confirmed)

```
theorem Ideal.minimalPrimes_sInf_of_finite_of_isPrime {R : Type*} [CommSemiring R]
    (s : Set (Ideal R)) (hfin : s.Finite) (hs : ∀ p ∈ s, p.IsPrime) :
    (sInf s).minimalPrimes = {p | p ∈ s ∧ ∀ q ∈ s, q ≤ p → p ≤ q}
```

For a **finite family of prime ideals** `s`, the minimal primes of its intersection `sInf s`
are exactly the **inclusion-minimal members** of `s`.

- **Hypotheses (minimal, build-confirmed):** `[CommSemiring R]` + `s.Finite` + `∀ p ∈ s, p.IsPrime`.
  No `Noetherian`, no `Field`, no `CommRing` — **generalised `[CommRing R] → [CommSemiring R]`**
  vs the original SPIKE (the build accepts it: the proof uses only `IsPrime.inf_le'`,
  `Finset.inf_id_eq_sInf`, `Set.Finite.coe_toFinset`/`mem_toFinset`, `sInf_le`, `le_antisymm`,
  all `CommSemiring`-valid).
- **Name = content:** `minimalPrimes_sInf` = "the minimal primes of an `sInf`"; `_of_finite_of_isPrime`
  = the two extra hypotheses. Distinct from Mathlib's `Ideal.sInf_minimalPrimes` (which is
  `sInf I.minimalPrimes = I.radical`, a different object/word-order). Mathlib has only that radical
  form — this finite-family packaging is a genuine small gap.
- **Proof:** prime avoidance via `Ideal.IsPrime.inf_le'` (`sInf s` = the finite `Finset.inf`,
  so a prime `P ⊇ sInf s` contains some member of `s`); both `⊆`/`⊇` inclusions of the set extensionality.

## Sibling-clash check (lean/CLAUDE.md gate) — CLEARED

- `rg minimalPrimes_sInf_of_finite` over all of Mathlib: **0 hits** (no clash).
- `rg` over `DLNFibre/`: the name now lives only in `MinimalPrime/Finite.lean` (def) + one qualified
  call in `SigmaComponents.lean`. No stale duplicate.
- No existing `Ideal.minimalPrimes_sInf*` in Mathlib's `MinimalPrime/` (only `sInf_minimalPrimes`),
  so the `Ideal.`-qualified name is unambiguous.

## Re-pointed consumers

- `lean/DLNFibre/Core/SigmaComponents.lean`:
  - Added `import DLNFibre.Core.MinimalPrime.Finite`.
  - **Deleted** the moved theorem + its section heading (no duplicate).
  - `minimalPrimes_sigmaIdeal_eq` now calls `Ideal.minimalPrimes_sInf_of_finite_of_isPrime`
    (qualified) and its docstring cross-references the new home.
  - The DLN-specific rest (`orbitIdeals`, `sigmaIdeal`, `sigmaIdeal_eq_sInf_orbitIdeals`,
    `minimalPrimes_sigmaIdeal_eq`, the `(2,2,2)` witnesses) stays local, unchanged in content.
- `lean/DLNFibre.lean` (single-writer aggregator): explicit `import DLNFibre.Core.MinimalPrime.Finite`
  added at the end (it was already pulled in transitively via `SigmaComponents`).

## L2 (transitive-consumer sweep) — done

`rg minimalPrimes_sInf_of_finite_of_isPrime` across all `DLNFibre/`: only the def + the one
`SigmaComponents` call site + the `SigmaComponents` docstring ref. **Full aggregator build** (not just
the touched module) run to catch unqualified/transitive consumers — green.

## Gate status

- **Build:** `./scripts/lb DLNFibre` (full aggregator) **green — 3820 jobs**.
  (Pre-existing `longLine` warnings only, in untouched files; the new module is longLine-clean;
  the two `SigmaComponents` longLines at 174–175 are pre-existing caveat-docstring text, not my edits.)
- **Sorries:** `scripts/sorries` = **0 sorry, 0 #exit, 0 native_decide, 0 axiom**.
- **Axioms:** `#print axioms Ideal.minimalPrimes_sInf_of_finite_of_isPrime` =
  **`[propext, Classical.choice, Quot.sound]`** (the `classical` is for `DecidableEq` in the avoidance step).

## Holes / surprises

- **Surprise (good):** the lemma generalises cleanly to `[CommSemiring R]` — recorded as the final
  hypothesis (was `[CommRing R]` in the SPIKE). This is strictly more reusable for an upstream move.
- No holes. The lemma was already fully general (no `RepCoord`/`Tuple`); this rung is pure re-home +
  hygiene + one hypothesis-weakening.
