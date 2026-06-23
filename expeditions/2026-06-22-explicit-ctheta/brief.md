# Expedition brief — explicit `(C, θ)` for an arbitrary dimension vector

**Branch:** `expedition/explicit-ctheta-arbitrary-d` (off `dev`, worktree `explicit-ctheta`).
**Opened:** 2026-06-22, following the merge of `expedition/perm-invariance` (PR #6).

## Central question

The landed explicit closed-form `(C, θ)` — `cValue`/`cTheta` (Thm 7.10) and the QIP equality
(Thm 6.1) — are gated on **`Monotone d`**. The just-merged permutation-invariance work provides the
**sort bridge** (`cCodim_comp_sort` / `numTop_comp_sort`: `(C,θ)` of any `d` equals that of its
monotone rearrangement `d ∘ Tuple.sort d`). Compose the two to give an **explicit closed-form
`(C, θ)` for an ARBITRARY (not-necessarily-monotone) `d`**, closing the Bundle-1 "remaining" item the
roadmap flags ("relating `d` to its sorted form … not free").

## Route (all ingredients landed)

For `1 ≤ N` and `r ≤ min d` (the range where `(C,θ)` are defined; non-emptiness discharged by
`kostantPartitions_nonempty_of_le`):

- **C:** `cCodim d r` =[`cCodim_rankShift`]= `cCodim (dminus d r) 0`
  =[`cCodim_comp_sort`]= `cCodim ((dminus d r) ∘ sort) 0`
  =[`cCodim_eq_qipMin`, `Monotone`]= `qipMin (…)`
  =[`qipMin_eq_cValue`]= `cValue ((dminus d r) ∘ Tuple.sort (dminus d r))`.
- **θ:** the same chain via `numTop_rankShift`, `numTop_comp_sort`, `numTop_zero_eq_cTheta`
  (`CThetaThetaBridge`) → `cTheta ((dminus d r) ∘ Tuple.sort (dminus d r))`.
- **Discharges:** `Monotone (d ∘ Tuple.sort d)` (Mathlib `Tuple.sort` lemma);
  `kostant_nonempty_iff_qipFeasible_nonempty` (`CThetaThetaBridge`) for the QIP-feasibility side.

## Deliverables

1. New `Core` module (`CThetaArbitrary` or similar): explicit `cCodim`/`numTop` for arbitrary `d`,
   `r = 0` and general `r`, with the `Monotone`-free statements above. Aggregated.
2. A **non-monotone witness** (e.g. `(2,3,2)` / `(1,2,1)`) checked by `decide +kernel`: `cCodim` =
   `cValue(sorted)`, `numTop` = `cTheta(sorted)` — showing it fires off the monotone case.
3. **ROADMAP refresh** (folded in): mark Cor 5.10 / Thm 5.5 / the Σ̄^r-aggregate reading as Proved
   (they are, post-PR #6), and mark this arbitrary-`d` explicit formula as Proved.

## Closing criterion

Green, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`; the arbitrary-`d` explicit
`(C,θ)` stated + witnessed; ROADMAP updated; reviewer-SOUND; PR → `dev`.

## Scope guards

- **Network-free `Core` only** — never import `DLNFibre.DLN`; nothing named `rlct_`.
- **No collision with the live aoyagi expedition** (Bundle 4 / RLCT analytic, in the main checkout) —
  this is pure Bundle-1 combinatorics on landed bricks.
