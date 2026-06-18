---
title: "Statement card — the paper predicate CM⁺_d (CMPlus) and the realizability ↔ CMPlus equivalence"
status: reviewed
topics: [formalisation, kostant, cor-2.9, cmplus, dimension-equations, equiv]
created: "2026-06-18"
updated: "2026-06-18"
---

# Card — CMPlus (the paper's CM⁺_d, standalone) ↔ realizability

Closes PR #1 deep-review point 1. The existing `KostantPartition d` carrier is **image-coded** — it
bakes "realizable by a tuple" into the carrier (`m ∈ kostantArrayOfRank '' Set.range (rankFn d) ∧
IsKostantArray m`). The paper (Le Halleur–Rimányi 2024, p.~8) defines `CM⁺_d` **independently**:
upper-triangular nonnegative multiplicity arrays satisfying the dimension equations
`d_k = ∑_{i ≤ k ≤ j} m_{ij}`. This card exposes that standalone predicate (`CMPlus`) and proves it
coincides with realizability, so the API now carries the genuine paper-side object.

- **Lean:** `DLNFibre.Core.CMPlus`, `cMPlus_kostantArrayOfRank`, `kostantArrayOfRank_rankFn_realizer`,
  `cMPlus_iff_mem_image`, `kostantPartitionCMPlusEquiv`, `orbitCMPlusEquiv`
  (`lean/DLNFibre/Core/OrbitKostant.lean`, SHA pending controller commit).

- **The predicate (standalone).**
  `CMPlus (d : Fin (N+1) → ℕ) (m : SuppArray (N:ℤ) ℤ) : Prop :=`
  `IsKostantArray m ∧ ∀ k : Fin (N+1), (d k : ℤ) = cumul (N:ℤ) m.1 (k:ℤ) (k:ℤ)`.
  `IsKostantArray m` is nonneg + `j < i → m_{ij}=0`. The dimension-equation sum `∑_{i ≤ k ≤ j} m_{ij}`
  is exactly `cumul` on the **diagonal** `(k,k)` (`cumul N m k k = ∑_{a ≤ k ≤ b} m_{ab}`). **No
  reference to `rankFn`/realizability** — the purely combinatorial paper definition.

- **Forward (realizable ⟹ CMPlus).** `cMPlus_kostantArrayOfRank (A : Tuple d) :`
  `CMPlus d (kostantArrayOfRank (rankFn d A))`. `IsKostantArray` from `kostantArrayOfRank_isKostant`
  (the bar-count bridge); the diagonal equation from `cumul_kostantArrayOfRank_of_le` +
  `rankPattern_self` (`r_{kk} = d_k`).

- **Reverse (CMPlus ⟹ realizable, the substantive one).**
  `kostantArrayOfRank_rankFn_realizer (m) (hm : CMPlus d m) :`
  `kostantArrayOfRank (rankFn d (realizer m hm)) = m`. The realizer is the explicit
  `⊕_{(i,j)} M_{ij}^{m_{ij}}` (interval direct sum) carrying `(m_{ij}).toNat` copies of each bar,
  cast over `d`. Built from:
  - `CopyIndex m := Σ p : Fin(N+1)², Fin (m_{p}).toNat`, `listOfArray m`, `copyBar`;
  - `multiplicityArray_listOfArray : multiplicityArray (listOfArray m) = m.1` — via the bar-count
    bridge `barMult_eq_card_fiber` and the fibre equiv `Equiv.sigmaSubtype` (`card_copyBar_fiber`),
    with the off-`[0,N]²`/below-diagonal vanishing matching `IsKostantArray`;
  - `foldDim_listOfArray : foldDim (listOfArray m) = d` (the **only** use of the diagonal CMPlus
    equation: `foldDim t = r_{tt}(⊕) = cumul (mult) t t = cumul m t t = d_t`);
  - `realizer m hm := foldDim_listOfArray m hm ▸ intervalDirectSum (listOfArray m)`;
  - `rankPattern_realizer : (r_{ij}(realizer) : ℤ) = cumul N m.1 i j` (via `rankPattern_transport` +
    `rankPattern_intervalDirectSum_eq_cumul` + `multiplicityArray_listOfArray`);
  - assembly via `diff_cumul` on the upper triangle, `IsKostantArray` below the diagonal.
  **Subtlety (load-bearing):** the diagonal CMPlus equations only pin `foldDim L = d`; the *whole*
  upper-triangular rank pattern is pinned by `m` itself (it is the multiplicity array), not by the
  diagonal.

- **The characterization + equivs.**
  `cMPlus_iff_mem_image (m) : CMPlus d m ↔ (m ∈ kostantArrayOfRank '' Set.range (rankFn d) ∧ IsKostantArray m)`.
  `kostantPartitionCMPlusEquiv d : KostantPartition d ≃ { m // CMPlus d m }` (via `subtypeEquivRight`).
  `orbitCMPlusEquiv d : Quotient (orbitSetoid d) ≃ { m // CMPlus d m }` — the headline retargeted onto
  the paper object, `⟦A⟧ ↦ kostantArrayOfRank (rankFn d A)` (`orbitCMPlusEquiv_mk`, by `rfl`). The
  existing `orbitKostantPartitionEquiv` (image-coded codomain) is kept unchanged; this is additive.

- **Witness.** `cMPlus_mWitnessSupp : CMPlus dWitness mWitnessSupp` where
  `mWitnessSupp := ⟨mWitness, supported_mWitness⟩` is the paper's last partition of `(2,2,2)`
  (`m₀₀=m₀₁=m₁₂=m₂₂=1`); diagonal equations `cumul 2 mWitness k k = 2 = d_k` by kernel `decide`. And
  it is realized — `kostantArrayOfRank (rankFn dWitness (realizer mWitnessSupp _)) = mWitnessSupp`
  over `ℚ`, directly from the reverse-direction theorem.

- **Assumed.** `Field k` (the realizer is a tuple over a field; `foldDim_listOfArray` instantiates the
  rank identity at `ℚ`, which suffices because the multiplicity array is field-free).
- **Cited.** none new; reuses `kostantArrayOfRank_isKostant`, `cumul_kostantArrayOfRank_of_le`,
  `rankPattern_self`, `rankPattern_intervalDirectSum_eq_cumul`, `barMult_eq_card_fiber`,
  `rankPattern_transport`, `diff_cumul`, and Mathlib `Equiv.sigmaSubtype` / `Fintype.equivFin` /
  `subtypeEquivRight`.
- **Status.** sorry-free; whole library 0 sorry/axiom/native_decide.
  `#print axioms` on `orbitCMPlusEquiv`, `cMPlus_iff_mem_image`, `kostantArrayOfRank_rankFn_realizer`,
  `cMPlus_kostantArrayOfRank` → `[propext, Classical.choice, Quot.sound]`.

## Fidelity (reviewed — PASS)

Independent reviewer (with decorrelated Codex, gpt-5.1-codex-max xhigh) verdict **PASS** on all four
points: (1) `CMPlus` is the standalone predicate — `IsKostantArray` (nonneg, `i ≤ j`-supported) plus
the dimension equations, no `rankFn`/realizability in the definition; the name `CMPlus`/`CM⁺` denotes
the `ℕ`-valued `CM⁺_d` (not the `ℤ`-valued `CM_d`); (2) `cumul N m k k = ∑_{0≤a≤k≤b≤N} m_{ab}` matches
the paper's `d_k = ∑_{i≤k≤j} m_{ij}` (no spurious/missing terms — `a≤k≤b` already forces `a≤b`); (3)
both directions genuine and non-circular — Codex confirmed the diagonal equation is *necessary* (an
`IsKostantArray` with wrong diagonal sums realizes over a different dimension vector), so the reverse
`m = m` conclusion is not vacuous; the diagonal equation is used only in `foldDim_listOfArray`, the
upper triangle pinned by `m` itself; (4) `orbitCMPlusEquiv` lands in `{ m // CMPlus d m }`, name =
content. No overclaim in the new docstrings.

One report-only finding, **pre-existing** (not this work): a stale doc reference at OrbitKostant.lean
~line 232 cited a non-existent `kostantArrayOfRank_eq_barMult`; corrected in this commit to
`kostantArrayOfRank_isKostant` (the actual bridge fact). No mathematical content affected.
