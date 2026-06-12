---
title: "Thread 03 — Prop 3.1a inclusion-exclusion inversion (rungs 2-3)"
status: sorry-free
topics: [rank-pattern, kostant, inclusion-exclusion, prop-3.1, inversion]
created: "2026-06-12"
updated: "2026-06-12"
---

# Thread 03 — Prop 3.1a: the inclusion–exclusion inversion (rungs 2–3)

Module: `lean/DLNFibre/Core/RankPattern.lean` (namespace `DLNFibre.Core`), network-free, ~320 lines.
(Persisted by the controller from the formaliser's return — the subagent hit a file-write guard.)

## What landed

The **abstract** Prop 3.1a inversion (Le Halleur–Rimányi §2, `prop:mr_comparison`): over an
`AddCommGroup R`, the cumulative map `S = cumul N` and the four-term finite-difference map `T = diff`
on integer-indexed arrays are mutually inverse.

- `cumul N m i j = ∑_{0≤k≤i} ∑_{j≤l≤N} m k l` (the paper's `r_{ij}=∑_{k≤i≤j≤l} m_{kl}`).
- `diff r i j = r_{ij} − r_{i,j+1} − r_{i−1,j} + r_{i−1,j+1}` (out-of-range `= 0`).
- Headline: `diff_cumul : diff (cumul N m) = m` and `cumul_diff : cumul N (diff r) = r` (each under
  `m`/`r` vanishing for `i<0` and `j>N`); packaged as `cumulDiffEquiv N : SuppArray N R ≃ SuppArray N R`.

Verbatim:
```lean
theorem diff_cumul (N : ℤ) (m : ℤ → ℤ → R)
    (hi : ∀ i j, i < 0 → m i j = 0) (hj : ∀ i j, N < j → m i j = 0) : diff (cumul N m) = m
theorem cumul_diff (N : ℤ) (r : ℤ → ℤ → R)
    (hi : ∀ i j, i < 0 → r i j = 0) (hj : ∀ i j, N < j → r i j = 0) : cumul N (diff r) = r
noncomputable def cumulDiffEquiv (N : ℤ) : SuppArray N R ≃ SuppArray N R
```

## Encoding decision (the crux) + the box→half-plane correction

Arrays are **total `ℤ → ℤ → R`**; "out of range = 0" is a **support hypothesis**, not an in-formula
guard (rejected: guarded `Fin`, padded `Fin (N+2)` — coercion tax). Both 2-D maps decouple into
commuting 1-D row (`i`) and column (`j`) operators, so each inversion is a one-line telescope.

**Correction (a real subtlety, not a fudge):** the square box `0≤i,j≤N` is the WRONG support invariant
— `cumul` saturates at `i>N`, `diff` leaks to `i=N+1`, so neither map preserves the box. The correct,
closed-under-both invariant is the **half-plane** `Supported N f := (∀ i j, i<0→f=0) ∧ (∀ i j, N<j→f=0)`
— exactly the round-trip hypothesis. `supported_cumul` (unconditional) and `supported_diff` prove
closure, giving the guard-free `Equiv`. The paper's finite triangular arrays are a subset.

## Witness (in-file, non-vacuity)

`N=2`, `ℤ`, `mWitness` = the `(2,2,2)` Kostant partition `m₀₀=m₀₁=m₁₂=m₂₂=1`. By kernel `decide`:
`cumul` gives diagonal `(2,2,2)` (recovers `d`) + off-diagonal `(1,0,1)`; `diff (cumul m) = m` and the
`cumulDiffEquiv` round-trip.

## Build / audit status

- `lake build` (whole lib) green, 1794 jobs; `scripts/sorries` → 0 across the board.
- `#print axioms` on `diff_cumul`/`cumul_diff`/`cumulDiffEquiv` → only `[propext, Classical.choice, Quot.sound]`.
- Cosmetic: one info `Try this: abel_nf` at line 127 (harmless; cleanup candidate).

## Deferred (probed, sharp note in-module)

`submult d A i j = A_j⋯A_{i+1}`, the bridge `mult = submult 0 (last)`, and `rankPattern := (submult).rank`.
*Obstacle:* `submult` has a **variable lower bound** `i`, so its return type `Matrix (Fin (d j)) (Fin (d i))`
makes the empty-product base sit at a variable index, forcing a dependent `Eq.mpr`/`▸` cast that destroys
`multPrefix`'s clean `rfl`-step pattern. Backed out (bedrock). *Recommended:* (a) define on the shifted
tail tuple `A' k = A (i+k)` over `d' k = d (i+k)`, recover via `multPrefix` + a reindexing bridge; or (b)
a `List.prod` build. Self-contained successor; the inversion does not depend on it.

## Friction

`abel` not `ring` (`R` an `AddCommGroup`; `import Mathlib.Tactic.Abel`). `Mathlib.Algebra.BigOperators.Ring.Basic`
removed at the v4.29 pin. Integer `Icc` insertion via `ext; simp [mem_insert, mem_Icc]; omega`. Several
Codex-suggested lemma names (`Finset.Icc_pred_right`, `sum_Icc_succ_top` for Int) not real at the pin —
helpers (`Icc_insert_top`/`_bot`, `sum_Icc_diffRow`/`_diffCol`) proved directly.

## For the controller / open precision question

- **`cumulDiffEquiv` naming.** The equiv is the *abstract* cumul↔diff inversion (no `Matrix.rank`).
  Does the name `cumulDiffEquiv` overclaim (suggest matrix rank patterns) vs the content (the
  inclusion-exclusion bijection)? → flagged to the reviewer (precision); candidate rename `cumulDiffEquiv`.

---

## Statement card (DRAFT — Prop 3.1a)

> **Claim (Prop 3.1a).** The cumulative map `S` (`r_{ij}=∑_{k≤i≤j≤l} m_{kl}`) and the four-term
> finite-difference map `T` (`m_{ij}=r_{ij}−r_{i,j+1}−r_{i−1,j}+r_{i−1,j+1}`, out-of-range `=0`) on
> integer-indexed arrays over an abelian group are mutually inverse.
>
> - **Lean:** `DLNFibre.Core.diff_cumul`, `DLNFibre.Core.cumul_diff`, `DLNFibre.Core.cumulDiffEquiv`
>   (`lean/DLNFibre/Core/RankPattern.lean` @ `32c8048`)
> - **Gloss.** Over any `AddCommGroup R`, for arrays `ℤ→ℤ→R` vanishing for `i<0` and `j>N`:
>   `diff (cumul N m) = m`, `cumul N (diff r) = r`; packaged as an `Equiv` on the supported-array subtype.
> - **Proved.** Both inversions + the bijection, unconditionally, by 2-D telescoping; `N=2` `(2,2,2)`
>   witness by kernel `decide`.
> - **Assumed.** Arrays vanish for `i<0` and `j>N` (the "out of range = 0" convention; the exact
>   hypothesis the inversion needs, closed under both maps).
> - **Cited.** none.
> - **Deferred.** Prop 3.1b — an actual tuple's `rankPattern` (`= rank(A_j⋯A_{i+1})`) equals `cumul` of
>   its type-A Gabriel multiplicities; needs rung 4. Also the `submult`/`rankPattern` matrix-side defs.
> - **Status.** sorry-free + reviewed (thread 04; the `rankPatternEquiv`→`cumulDiffEquiv` rename and the stale-box-docstring fix applied).
