# Statement card — M2: the `N = 1` Durfee identity

Thread 06 (perm-invariance expedition). The single classical `q`-series input the PEEL transfer (M3)
rests on — pinned in thread 04 to be the *only* such input.

> **Claim.** Over `ℤ⟦X⟧`, for all `a b : ℕ`,
> `P a * P b = ∑_{r=0}^{min a b} X^{(a-r)(b-r)} · P (a-r) · P r · P (b-r)`,
> where `P` is the inverse q-Pochhammer of `Core.QSeries` (M1).
>
> - **Lean:** module `DLNFibre.Core.QSeriesDurfee` (`lean/DLNFibre/Core/QSeriesDurfee.lean` @ `9d408a3`,
>   branch `expedition/perm-invariance`; SHA pinned by the controller at commit). Headline: `durfee`.
>   Ladder (all green, sorry-free):
>   - defs: `durfeeTerm`, `durfeeSum`
>   - peel: `P_mul_one_sub_succ` (`P (s+1) · (1 − X^{s+1}) = P s`)
>   - base: `durfee_base`; LHS descent: `lhs_desc`; scalar split: `one_sub_pow_split`
>   - per-term: `A_term`, `B_term`; boundary zeros: `A_top_zero`, `B_zero_at_zero`, `B_missing_top_zero`
>   - sum descents: `A_sum_desc`, `B_sum_desc` (the reindex `r = s+1`, via `Finset.sum_range_succ'`)
>   - RHS descent: `rhs_desc`; unit fact: `one_sub_X_pow_ne_zero`; headline: `durfee`
> - **Proof.** Route B (thread 06; exact-verified to degree 55, Codex-converged): induction on `b`. Both
>   sides descend under `× (1 − X^{b+1})` (`lhs_desc`, `rhs_desc`); `1 − X^{b+1}` is a **unit** in `ℤ⟦X⟧`
>   (constant term `1`, via `PowerSeries.isUnit_iff_constantCoeff`), so the inductive step cancels by
>   `IsUnit.mul_right_injective`. No coefficient combinatorics, no Gaussian binomials.
> - **Proved.** Unconditionally, axiom-clean. `#print axioms durfee = [propext, Classical.choice,
>   Quot.sound]`. Builds on M1 (`Core.QSeries`: `P`, `P_succ`, `geomFactor_mul_one_sub`, `P_zero`).
> - **Assumed / Cited.** None — every step from Mathlib `PowerSeries`/`Finset`/`Nat` primitives. (`q`-series
>   support is absent from Mathlib v4.29; this reproves the needed fragment from scratch.)
> - **Status.** sorry-free, green, axiom-clean. (Controller-written inline; not yet independently AUDITed.)

## Build / hygiene
- `lake build DLNFibre.Core.QSeriesDurfee`: green, 0 long-line warnings.
- Full aggregate `lake build`: green (3686 jobs); `scripts/sorries`: 0 sorry / 0 axiom.
- Imports `DLNFibre.Core.QSeries` + `Mathlib.Tactic.LinearCombination` + `Mathlib.RingTheory.PowerSeries.Inverse`;
  no `DLN.*`. Aggregator: `import DLNFibre.Core.QSeriesDurfee` appended.

## v4.29 gotchas found
- `linear_combination` needs an explicit `import Mathlib.Tactic.LinearCombination` (not transitive here).
- `PowerSeries.isUnit_iff_constantCoeff` lives in `Mathlib.RingTheory.PowerSeries.Inverse` (not transitive);
  holds for `[Ring R]` (so `ℤ⟦X⟧` qualifies). `ℤ⟦X⟧` does NOT auto-synthesize `IsLeftCancelMulZero`, so
  cancel via the unit route, not `mul_left_cancel₀`.
- `le_or_lt` is not in scope at this pin — use `by_cases h : a ≤ b` (`omega` reads `¬ a ≤ b`).
