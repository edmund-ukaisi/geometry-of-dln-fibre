---
title: "Statement card — the literal orbit ↔ Kostant-partition bijection (Cor 2.9)"
status: sorry-free
topics: [formalisation, kostant, cor-2.9, equiv, quotient, multiplicity-array]
created: "2026-06-18"
updated: "2026-06-18"
---

# Card — the literal orbit ↔ Kostant-partition bijection (Cor 2.9)

Closes the "Deferred" item of thread 16's first card: the explicit composition with
`cumulDiffEquiv` that presents the right-hand side as **multiplicity arrays (Kostant partitions)**
rather than rank patterns. Additive — `orbitKostantEquiv` and `RealizableRank` are kept exactly.

- **Lean:** `DLNFibre.Core.orbitKostantPartitionEquiv` (`lean/DLNFibre/Core/OrbitKostant.lean`,
  SHA pending controller commit).
- **Signature.**
  `(d : Fin (N+1) → ℕ) : Quotient (orbitSetoid d) ≃ RealizableKostant d`
  where `RealizableKostant d := ↥(kostantArrayOfRank '' Set.range (rankFn d))`,
  `kostantArrayOfRank r := (cumulDiffEquiv (R := ℤ) (N := (N:ℤ))).symm (embedRank r) : SuppArray (N:ℤ) ℤ`,
  and `embedRank : (Fin (N+1) → Fin (N+1) → ℕ) → SuppArray (N:ℤ) ℤ` casts `ℕ→ℤ` and extends the
  `Fin`-index to `ℤ` by `0` outside `[0,N]²`. Computation lemma
  `orbitKostantPartitionEquiv_mk : ⟦A⟧ ↦ kostantArrayOfRank (rankFn d A)` (= `diff (rankFn A)`), by `rfl`.
- **Gloss.** The set of `G_d`-orbits of composable matrix tuples is in bijection with the realizable
  **Kostant partitions** of `d` — the multiplicity arrays `m̄ = diff r` — via `⟦A⟧ ↦ diff (rankFn A)`.
  This is `orbitKostantEquiv` (orbits ↔ rank patterns) composed with one more inversion,
  `RankPattern.cumulDiffEquiv.symm` (rank patterns ↔ multiplicity arrays).
- **Proved.** the `Equiv`: `orbitKostantEquiv` ∘ (`Equiv.Set.image` of `kostantArrayOfRank`).
  `embedRank` injective (`embedRank_injective`), `kostantArrayOfRank` injective from
  `cumulDiffEquiv`'s symm-injectivity (`kostantArrayOfRank_injective`). Concrete `(2,2,2)`
  multiplicity values exhibited by kernel `decide`: on `i ≤ j`, `m̄₀₀ = m̄₀₁ = m̄₁₂ = m̄₂₂ = 1`,
  `m̄₁₁ = m̄₀₂ = 0` (the paper's `mWitness`). Literal-equiv witness on `tupleWitnessQ` by `rfl`.
- **Assumed.** `Field k`.
- **Cited.** none new; reuses `orbitKostantEquiv`, `RankPattern.cumulDiffEquiv`, Mathlib
  `Equiv.Set.image`.
- **Caveat (next to the claim).** `kostantArrayOfRank (rankFn d A) = diff (embedRank (rankFn d A))`
  equals the paper's Kostant partition **on the support `i ≤ j`** (where Kostant partitions live).
  Below the diagonal it carries artifacts of `rankFn`'s lower-triangle-zero convention (e.g.
  `(diff rWitness)_{1,0} = -3`). The bijection is exact regardless; `RealizableKostant` is the genuine
  bijection image. This is documented in `kostantArrayOfRank` / `orbitKostantPartitionEquiv` and the
  witness block.
- **Status.** sorry-free; `#print axioms orbitKostantPartitionEquiv` →
  `[propext, Classical.choice, Quot.sound]`.

## Fidelity question for the reviewer

Does "literal Kostant partition" hold, given the lower-triangle artifact? The honest reading: the
codomain object **is** the Kostant partition on `i ≤ j` (its natural support), and the equiv is exact.
The artifact is a presentation byproduct of the lossy `rankFn` encoding (which zeroes below the
diagonal), not a defect of the bijection. A cleaner-still codomain would restrict to `i ≤ j`, at the
cost of breaking the clean `cumulDiffEquiv` composition. Reviewer to adjudicate whether the documented
caveat suffices or the name should be qualified.
