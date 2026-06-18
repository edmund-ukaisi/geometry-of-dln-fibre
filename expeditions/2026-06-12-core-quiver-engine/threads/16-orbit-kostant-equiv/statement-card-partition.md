---
title: "Statement card — orbits ↔ the multiplicity-array (diff) form of rank patterns (towards Cor 2.9)"
status: reviewed
topics: [formalisation, kostant, cor-2.9, equiv, quotient, multiplicity-array]
created: "2026-06-18"
updated: "2026-06-18"
---

# Card — orbits ↔ the second-difference form of realizable rank patterns

Closes the "Deferred" item of thread 16's first card: the explicit composition with
`cumulDiffEquiv` that takes the right-hand side one inversion past rank patterns, to the
multiplicity-array (`diff`) form. Additive — `orbitKostantEquiv` and `RealizableRank` are kept
exactly. Reviewed (fidelity) before commit; the name was corrected from `orbitKostantPartitionEquiv`
to `orbitDiffArrayEquiv` per the review finding (see Fidelity below).

- **Lean:** `DLNFibre.Core.orbitDiffArrayEquiv` (`lean/DLNFibre/Core/OrbitKostant.lean`,
  SHA pending controller commit).
- **Signature.**
  `(d : Fin (N+1) → ℕ) : Quotient (orbitSetoid d) ≃ RealizableDiffArray d`
  where `RealizableDiffArray d := ↥(diffArrayOfRank '' Set.range (rankFn d))`,
  `diffArrayOfRank r := (cumulDiffEquiv (R := ℤ) (N := (N:ℤ))).symm (embedRank r) : SuppArray (N:ℤ) ℤ`,
  and `embedRank : (Fin (N+1) → Fin (N+1) → ℕ) → SuppArray (N:ℤ) ℤ` casts `ℕ→ℤ` and extends the
  `Fin`-index to `ℤ` by `0` outside `[0,N]²`. Computation lemma
  `orbitDiffArrayEquiv_mk : ⟦A⟧ ↦ diffArrayOfRank (rankFn d A)` (= `diff (rankFn A)`), by `rfl`.
- **Gloss.** The set of `G_d`-orbits of composable matrix tuples is in bijection with the realizable
  second-difference arrays of `d` — `⟦A⟧ ↦ diff (rankFn A)`. This is `orbitKostantEquiv` (orbits ↔
  rank patterns) composed with one more inversion, `RankPattern.cumulDiffEquiv.symm` (rank patterns ↔
  second-difference arrays). **On the support `i ≤ j` the image is exactly the paper's Kostant
  partition** `m̄` (the interval multiplicities); below the diagonal it carries artifacts of `rankFn`'s
  lower-triangle-zero convention.
- **Proved.** the `Equiv`: `orbitKostantEquiv` ∘ (`Equiv.Set.image` of `diffArrayOfRank`).
  `embedRank` injective (`embedRank_injective`), `diffArrayOfRank` injective from `cumulDiffEquiv`'s
  symm-injectivity (`diffArrayOfRank_injective`). Concrete `(2,2,2)` values by kernel `decide`: on
  `i ≤ j`, `m̄₀₀ = m̄₀₁ = m̄₁₂ = m̄₂₂ = 1`, `m̄₁₁ = m̄₀₂ = 0` (the paper's `mWitness`); and the
  below-diagonal artifact `(diff rWitness)_{1,0} = -3` (exhibited, so the overclaim cannot recur).
  Multiplicity-array-equiv witness on `tupleWitnessQ` by `rfl`.
- **Assumed.** `Field k`.
- **Cited.** none new; reuses `orbitKostantEquiv`, `RankPattern.cumulDiffEquiv`, Mathlib
  `Equiv.Set.image`.
- **Status.** sorry-free; `#print axioms orbitDiffArrayEquiv` → `[propext, Classical.choice, Quot.sound]`.

## Fidelity (reviewed)

A controller-style fidelity review (with decorrelated Codex) flagged that the original name
`orbitKostantPartitionEquiv` / type `RealizableKostant` / docstring "literal Cor 2.9" **overclaimed**:
a Kostant partition is by definition a nonnegative array supported on `i ≤ j`, but the codomain
elements carry negative below-diagonal entries (e.g. `-3`), so the *full* array is not a Kostant
partition. The review verified the strengthening fact that the `i ≤ j` part reads only on/above-diagonal
entries, hence is a genuine Kostant partition there. Fix applied (name = content): renamed to
`orbitDiffArrayEquiv` / `RealizableDiffArray`, struck "literal", stated precisely "the image is the
Kostant partition on `i ≤ j`", and added an in-file `decide` witness of the `-3` artifact.

## Roadmap (the genuinely-literal Cor 2.9 codomain)

Restricting the codomain to the nonnegative `i ≤ j` part recovers the literal "orbits ↔ Kostant
partitions" bijection. The review confirmed this is mathematically clean; it is left as a follow-up
because it needs the rank-pattern inequalities (to prove the `i ≤ j` diff entries are nonnegative for
every *realizable* rank pattern) and it gives up the guard-free full-square `cumulDiffEquiv`
composition. Bare extension — for the operator/controller to schedule.
