---
title: "Statement card — orbits ↔ literal Kostant partitions (Cor 2.9)"
status: sorry-free
topics: [formalisation, kostant, cor-2.9, equiv, quotient, kostant-partition]
created: "2026-06-18"
updated: "2026-06-18"
---

# Card — orbits ↔ literal Kostant partitions (Cor 2.9)

Closes the "Roadmap" item of the `statement-card-partition.md` card: the genuinely-literal Cor 2.9
codomain — the **nonnegative, `i ≤ j`-supported** multiplicity arrays. Additive — `orbitKostantEquiv`,
`RealizableRank`, `orbitDiffArrayEquiv`, `RealizableDiffArray` are kept exactly. The new equiv lands
in a literal Kostant-partition object with **no lower-triangle artifacts**.

- **Lean:** `DLNFibre.Core.orbitKostantPartitionEquiv` (`lean/DLNFibre/Core/OrbitKostant.lean`,
  SHA pending controller commit).
- **Signature.**
  `(d : Fin (N+1) → ℕ) : Quotient (orbitSetoid d) ≃ KostantPartition d`
  where
  - `KostantPartition d := { m : SuppArray (N:ℤ) ℤ // m ∈ kostantArrayOfRank '' Set.range (rankFn d) ∧ IsKostantArray m }`,
  - `IsKostantArray m := (∀ i j, 0 ≤ m.1 i j) ∧ (∀ i j, j < i → m.1 i j = 0)` (nonnegative, supported on `i ≤ j`),
  - `kostantArrayOfRank r := ⟨fun i j ↦ if i ≤ j then (diffArrayOfRank r).1 i j else 0, _⟩` —
    `diffArrayOfRank r` **truncated to `0` below the diagonal**.
  Computation lemma `orbitKostantPartitionEquiv_mk : ⟦A⟧ ↦ kostantArrayOfRank (rankFn d A)`, by `rfl`.
- **Gloss.** The set of `G_d`-orbits of composable matrix tuples is in bijection with the realizable
  **Kostant partitions** of `d` — the nonnegative, `i ≤ j`-supported multiplicity arrays — via
  `⟦A⟧ ↦` the truncated second-difference array `diff (rankFn A)` (the Kostant partition, with the
  below-diagonal `diff`-artifacts zeroed). This is the literal-codomain form of `orbitDiffArrayEquiv`:
  same bijection, genuine paper-side codomain.
- **Proved.**
  - **Bridge fact** `kostantArrayOfRank_isKostant A : IsKostantArray (kostantArrayOfRank (rankFn d A))`
    — every realizable truncated diff-array is nonnegative and `i ≤ j`-supported. Proof: via
    `Gabriel.exists_cumul_barMult A`, the truncation equals the bar-multiplicity array
    `barMult M birth death` (`embedRank (rankFn A) = cumul N barMult` on `i ≤ j`, so the four-term
    `diff` of one equals the four-term `diff` of the other = `barMult` by `diff_cumul`; below the
    diagonal both are `0`). `barMult` is a sum of `singleDelta` indicators, hence nonnegative; bars
    have `birth ≤ death`, hence `i ≤ j`-supported. **No new barcode lemma** — only truncation/`diff`
    bookkeeping over the existing barcode interface.
  - **Injectivity** `kostantArrayOfRank_injOn` (on `Set.range (rankFn d)`): truncation is invisible
    to `cumul` on the upper triangle (`cumul_truncBelow_of_le`), so
    `cumul (kostantArrayOfRank r) = embedRank r` there (`cumul_diff`); the truncated array therefore
    determines `rankFn` on `i ≤ j` (`embedRank_apply_fin`), and `rankFn` is `0` below the diagonal by
    convention. (Did not need the orbit theory — pure inversion.)
  - The `Equiv`: `orbitKostantEquiv ∘ rankKostantPartitionEquiv`, where the latter is
    `Equiv.Set.imageOfInjOn kostantArrayOfRank` composed with `Equiv.subtypeEquivRight` attaching the
    (total) `IsKostantArray` certificate.
  - **Witness (`(2,2,2)/ℚ`).** `orbitKostantPartitionEquiv` fires on `tupleWitnessQ` (by `rfl`).
    `kostantArrayOfRank rWitness = RankPattern.mWitness` **on the whole `ℤ × ℤ` plane** (the paper's
    Kostant partition: `1` at `(0,0),(0,1),(1,2),(2,2)`, rest `0`); the artifact entry `(1,0)`, which
    is `-3` in `diffArrayOfRank`, is `0` here. Per-entry `decide` + the truncation lemma.
- **Assumed.** `Field k`.
- **Cited.** none new; reuses `orbitKostantEquiv`, `Gabriel.exists_cumul_barMult`,
  `RankPattern.{cumul_diff, diff_cumul, supported_barMult}`, Mathlib `Equiv.Set.imageOfInjOn`,
  `Equiv.subtypeEquivRight`.
- **Deferred.** none for this statement.
- **Status.** sorry-free; `#print axioms orbitKostantPartitionEquiv` →
  `[propext, Classical.choice, Quot.sound]` (same for `_mk`, `kostantArrayOfRank_isKostant`,
  `kostantArrayOfRank_injOn`). Whole library `lake build` green; `scripts/sorries` reports 0.
  Awaiting independent fidelity review.

## Relation to the prior card

`statement-card-partition.md` delivers `orbitDiffArrayEquiv` (the `diff`-form, artifacts below the
diagonal) and explicitly roadmapped this literal restriction "needs the rank-pattern inequalities for
nonnegativity". This card discharges that: nonnegativity comes not from re-deriving rank-pattern
inequalities but from identifying the truncation with the manifestly-nonnegative `barMult` of a
Gabriel decomposition (`exists_cumul_barMult`, already in `Orbit.lean`). All three equivs now
coexist: `orbitKostantEquiv` (rank patterns) → `orbitDiffArrayEquiv` (diff form) →
`orbitKostantPartitionEquiv` (literal Kostant partitions).
