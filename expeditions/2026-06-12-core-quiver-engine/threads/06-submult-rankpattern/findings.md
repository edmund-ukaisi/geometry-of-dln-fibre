---
title: "Thread 06 — submult + matrix-side rank pattern (rung 4a)"
status: sorry-free
topics: [rank-pattern, submult, interval-product, matrix-rank, rung-4]
created: "2026-06-12"
updated: "2026-06-12"
---

# Thread 06 — `submult` and the matrix-side rank pattern (rung 4a)

Module: `lean/DLNFibre/Core/Submult.lean` (namespace `DLNFibre.Core`), network-free, imports
`DLNFibre.Core.Setup` (+ `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` for the witness rank).
Resolves the `submult`/`rankPattern` task `RankPattern.lean`'s deferred note parked. (Persisted by the
controller from the formaliser's return — subagent write-guard, as in thread 03.)

## What landed
`submult d A i j = A_j ⋯ A_{i+1} : Matrix (Fin (d j)) (Fin (d i)) k` (identity at `i=j`); the step
lemma `submult_succ` (the `multPrefix_succ` analogue); `submult_zero` (the `i=0` slice = `multPrefix`);
the bridge `mult_eq_submult : mult d A = submult d A 0 (last N)`; `rankPattern d A i j = (submult).rank`;
`rankPattern_self : r_{ii} = d_i` (`[Nontrivial k]`).

## Route: absolute-upper `Nat.leRec` (a THIRD route, neither shifted-tail nor List.prod)
Recurse on the upper index over `ℕ` via `Nat.leRec` from `i.val ≤ j.val`, `i` fixed, with a
function-valued motive `m ↦ (m<N+1) → Matrix (Fin (d ⟨m,_⟩)) (Fin (d i)) k`. The base `m=i.val` is `1`
(its endpoint `d ⟨i.val,_⟩` is `d i` by proof irrelevance on the `Fin` — no cast); the step
(`submultStep`, a named def for stable `Nat.leRec` reduction) prepends `A_m`. **No `finCongr`/reindex/`▸`
in any def or theorem** — the variable-base cast is *gone*, not merely localised. Beats the deferred
note's shifted-tail (one reindex per factor) and List.prod options; Codex (xhigh) independently ranked
`Nat.leRec` top (`codex/route-{prompt,answer}.md`).

## Witness ((2,2,2)/ℤ, on `Setup.tupleWitness`)
`submult 0 1 = A₁`, `submult 1 2 = A₂` (genuine `i≠0` slice), `submult 0 2 = A₂A₁ = [[1,2],[3,7]] = mult`,
the bridge, diagonal ranks `r_{ii}=d_i=2`, off-diagonal `r_{02}=2` (product is a unit over ℤ). All
sub-products computed algebraically via `submult_succ`/`_zero` then `decide` (direct `decide` on the
`Nat.leRec` term is blocked by its casework).

## Build / audit
- whole lib green (1795 jobs); `scripts/sorries` → 0; `#print axioms` on `submult`/`mult_eq_submult`/
  `rankPattern_self` → only `[propext, Classical.choice, Quot.sound]`. Controller-precision-checked
  (name = content; no overclaim; Prop 3.1b not asserted). Reviewer fidelity audit batched into the rung-4
  review (4b–4e).

## API choice (controller-confirmed)
`submult`/`rankPattern` take `(hij : i ≤ j)` as an **explicit** argument — keeps the return type honest
(`Matrix (Fin (d j)) (Fin (d i))` is correct only for `i ≤ j`) and matches the witness calls. Fine for
downstream 4b/4d.

## Scope / precision
Matrix-side rank-pattern object ONLY. `rankPattern = cumul` of Gabriel multiplicities (Prop 3.1b) is the
later rung (4d); nothing here is named as if it asserted the Gabriel decomposition.

---

## Statement card (DRAFT)

> **Claim.** For `A : Tuple d` over a `CommRing k` and `i ≤ j`, the interval sub-product
> `submult d A i j = A_j⋯A_{i+1}` is well-typed `Fin (d i) → Fin (d j)` (identity at `i=j`), the full
> product is its `0→last N` slice (`mult = submult 0 (last N)`), and `rankPattern` recovers `d_i` on the
> diagonal (`k` nontrivial).
>
> - **Lean:** `DLNFibre.Core.submult`, `submult_self`, `submult_succ`, `submult_zero`, `mult_eq_submult`,
>   `rankPattern`, `rankPattern_self` (`lean/DLNFibre/Core/Submult.lean` @ `<pin>`)
> - **Gloss.** `submult … (h : i ≤ j) : Matrix (Fin (d j)) (Fin (d i)) k` = ordered product of
>   `A_{i+1},…,A_j` (empty `= 1` at `i=j`); `submult_succ` = left-multiply step; `submult_zero` ties the
>   `i=0` slice to `multPrefix`; `mult_eq_submult` recovers `mult`; `rankPattern = (submult).rank`;
>   `rankPattern_self : r_{ii} = d_i`.
> - **Proved.** All of the above, unconditionally; no dependent cast in any statement.
> - **Assumed.** `CommRing k`; `Nontrivial k` for `rankPattern_self`; `i ≤ j` explicit.
> - **Cited.** none (Mathlib lemmas used in-proof, not as an external interface).
> - **Deferred.** `rankPattern = cumul` of Gabriel multiplicities (Prop 3.1b) — rung 4d.
> - **Status.** sorry-free; controller-precision-checked; reviewer audit batched into the rung-4 review.
