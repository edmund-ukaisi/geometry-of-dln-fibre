---
title: "Thread 16 — the orbit ↔ Kostant bijection as a single Equiv (Cor 2.9)"
status: open
topics: [formalisation, gabriel, orbit, kostant, cor-2.9, equiv, quotient]
created: "2026-06-13"
updated: "2026-06-13"
---

# Thread 16 — packaging the orbit ↔ Kostant bijection as an `Equiv`

**Type:** formalisation (tide), cosmetic packaging. **Environment:** MAIN checkout (branch
`expedition/core-quiver-engine`, HEAD `7e7bc5e`). New module left **UNTRACKED** for the controller to
commit — new module only; `Orbit.lean`, the aggregator, and all committed modules untouched.

**Module:** `lean/DLNFibre/Core/OrbitKostant.lean` (namespace `DLNFibre.Core`, network-free, `Field k`,
104 lines). **Build:** `lake build DLNFibre.Core.OrbitKostant` green (1797 jobs), **zero warnings**.
`scripts/sorries`: 0 sorry / 0 #exit / 0 native_decide / 0 axiom. `#print axioms orbitKostantEquiv`
→ `[propext, Classical.choice, Quot.sound]` (clean).

## What this thread did

Packaged the orbit ↔ Kostant correspondence (Cor 2.9) — whose content was already proved and audited
in `Orbit.lean` — as a single `Equiv` object.

### Chosen target type (reported, as asked)

**Realizable rank patterns**, `RealizableRank d := ↥(Set.range (rankFn d))`, where
`rankFn d A : Fin (N+1) → Fin (N+1) → ℕ := fun i j ↦ if h : i ≤ j then rankPattern d A i j h else 0`
is the rank pattern as a **total `ℕ`-function** (clean function equality). This is the cleanest
faithful target: it is *exactly* "the rank patterns that arise from some tuple", and the complete
invariant makes `rankFn` a complete `G_d`-invariant. The identification with **Kostant partitions of
`d`** (multiplicity arrays `m̄ = diff r`) is the already-formalised `RankPattern.cumulDiffEquiv`
(rank pattern ↔ multiplicity array); composing `orbitKostantEquiv` with it yields the multiplicity
(Kostant) form. The realizing tuple of any rank pattern is the interval direct sum `⊕ M^{m̄}`
(`Orbit.baseChange_normalForm`).

### Construction

- `orbitSetoid d` — the **genuine `G_d`-orbit relation** `A ≈ B ↔ ∃ P, P • A = B`, proved an
  `Equivalence` from the group action (`one_smul` / `mul_smul` / `inv_mul_cancel`).
- `rankFn_eq_iff_orbit` — `rankFn d A = rankFn d B ↔ ∃ P, P • A = B`, repackaging the complete
  invariant `Orbit.rankPattern_eq_iff_orbit` as total-function equality.
- `orbitKostantEquiv d` — `(Quotient.congrRight ((rankFn_eq_iff_orbit _ _).symm)).trans
  (Setoid.quotientKerEquivRange (rankFn d))`. The orbit relation **is** `Setoid.ker (rankFn d)` (the
  complete invariant), so the first isomorphism theorem for sets
  (`Setoid.quotientKerEquivRange`) gives the bijection onto `Set.range (rankFn d)`. Injectivity is the
  complete invariant; surjectivity is the `Set.range` target.
- `orbitKostantEquiv_mk` — the bijection sends `⟦A⟧ ↦ rankFn A` (by `rfl`).

Witness: the `(2,2,2)/ℚ` tuple (`tupleWitnessQ`) — `orbitKostantEquiv` sends `⟦tupleWitnessQ⟧` to
`rankFn tupleWitnessQ` (by `rfl`).

## Statement card

> **Card — the orbit ↔ Kostant bijection (Cor 2.9), packaged.**
> - **Lean:** `DLNFibre.Core.orbitKostantEquiv` (`lean/DLNFibre/Core/OrbitKostant.lean`, SHA pending controller commit)
> - **Signature.** `(d : Fin (N+1) → ℕ) : Quotient (orbitSetoid d) ≃ RealizableRank d` where `orbitSetoid d` is `A ≈ B ↔ ∃ P : BaseChangeGroup d, P • A = B` and `RealizableRank d := ↥(Set.range (rankFn d))`, with `orbitKostantEquiv_mk : ⟦A⟧ ↦ rankFn A`.
> - **Gloss.** The set of `G_d`-orbits of composable matrix tuples is in bijection with the realizable rank patterns of `d`, via `⟦A⟧ ↦ rankPattern A`. Realizable rank patterns biject with Kostant partitions of `d` by `RankPattern.cumulDiffEquiv` (rank ↔ multiplicity).
> - **Proved.** the `Equiv` (bijection): well-defined + injective from the complete invariant, surjective onto the realizable patterns.
> - **Assumed.** `Field k`.
> - **Cited.** none new; **reuses** `Orbit.rankPattern_eq_iff_orbit`, Mathlib `Setoid.quotientKerEquivRange`, `Quotient.congrRight`.
> - **Deferred.** the explicit composition with `cumulDiffEquiv` to present the right-hand side as multiplicity arrays (Kostant partitions) rather than rank patterns — a one-step repackaging; the rank↔Kostant bijection is already formalised.
> - **Status.** sorry-free.

## Net

The orbit ↔ Kostant bijection of Cor 2.9 is now a single `Equiv` object,
`Quotient (orbitSetoid d) ≃ RealizableRank d`, sorry-free and axiom-clean, with a concrete `(2,2,2)/ℚ`
witness. With this, rung 4 is fully packaged: complete invariant (`rankPattern_eq_iff_orbit`),
normal-form object (`baseChange_normalForm`), and the bijection (`orbitKostantEquiv`).
