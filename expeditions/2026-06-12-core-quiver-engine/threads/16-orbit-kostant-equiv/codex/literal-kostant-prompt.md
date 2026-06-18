<task>
Lean 4 + Mathlib (v4.29) design review. I have an existing bijection and want to ADD a corestricted one onto a "literal Kostant partition" codomain, with the LIGHTEST proof obligations.

CONTEXT (existing, all proved, zero sorry):
- `Tuple d` = composable matrix tuples for dim vector `d : Fin (N+1) → ℕ`.
- `orbitSetoid d : Setoid (Tuple d)` (G_d-orbit relation).
- `rankFn d A : Fin(N+1) → Fin(N+1) → ℕ` = rank pattern, ZEROED below the diagonal (j<i ↦ 0). Complete G_d invariant: `rankFn d A = rankFn d B ↔ same orbit`.
- `RealizableRank d := ↥(Set.range (rankFn d))`.
- `orbitKostantEquiv d : Quotient (orbitSetoid d) ≃ RealizableRank d`  (⟦A⟧ ↦ rankFn d A).
- `SuppArray (N:ℤ) ℤ := {f : ℤ→ℤ→ℤ // Supported}` (vanish i<0 and j>N).
- `cumul N`, `diff` : mutually inverse on SuppArray (`cumulDiffEquiv`); `diff_cumul`, `cumul_diff`.
- `embedRank r : SuppArray` casts `rankFn`-shaped r to ℤ-indexed, 0 outside [0,N]².
- `diffArrayOfRank r := cumulDiffEquiv.symm (embedRank r) = diff (embedRank r)`.
- `RealizableDiffArray d := ↥(diffArrayOfRank '' Set.range (rankFn d))`.
- `orbitDiffArrayEquiv d : Quotient (orbitSetoid d) ≃ RealizableDiffArray d` (⟦A⟧ ↦ diffArrayOfRank (rankFn d A)).
- KEY HELPER `exists_cumul_barMult A : ∃ M birth death, (∀ lam, birth lam ≤ death lam) ∧ (Kostant constraint) ∧ ∀ i≤j, (rankPattern A i j : ℤ) = cumul N (barMult M birth death) i j`. Here `barMult M birth death a b = ∑ lam, singleDelta (birth lam)(death lam) a b` is MANIFESTLY nonneg (sum of 0/1) and supported on `i ≤ j` (since birth ≤ death). And `diff (cumul N (barMult ...)) = barMult ...`.

THE SUBTLETY: `diffArrayOfRank (rankFn d A)` agrees with `barMult` (the true nonneg Kostant array) ONLY on `i ≤ j`. BELOW the diagonal it carries artifacts (e.g. value -3 at (1,0)) because `rankFn` zeroes the lower triangle while `cumul (barMult)` saturates there. So `diffArrayOfRank (rankFn d A)` itself is NOT nonneg and NOT below-diagonal-zero. The literal Kostant object must be the TRUNCATED array (= barMult): equals diffArrayOfRank on i≤j, 0 below.

GOAL: define `KostantPartition d` = the literal nonneg, i≤j-supported (j<i ↦ 0) realizable multiplicity arrays, and build `orbitKostantPartitionEquiv d : Quotient (orbitSetoid d) ≃ KostantPartition d`, ADDITIVELY (keep all existing defs).

I have two candidate routes and want the one with the least bespoke Equiv plumbing and least new proof:

ROUTE A (truncation map): define `kostantArrayOfRank r := ⟨fun i j ↦ if i ≤ j then diff (embedRank r) i j else 0, _supported_⟩`. Build `RealizableRank d ≃ KostantPartition d` as `Equiv.Set.image kostantArrayOfRank (Set.range (rankFn d)) hinj`, needing: (a) `kostantArrayOfRank` INJECTIVE on `Set.range (rankFn d)` only; (b) image lands in / equals the Kostant-predicate subtype. Then compose with orbitKostantEquiv.
  - injectivity worry: truncation loses below-diagonal; on realizable patterns the below-diagonal of diffArrayOfRank is determined, but proving injectivity of the truncation needs: equal-on-i≤j ⟹ equal rankPattern on i≤j (cumul only reads upper triangle) ⟹ same orbit ⟹ same rankFn. Non-trivial.

ROUTE B (recertify, via barMult equality): prove BRIDGE `∀ A, kostantArrayOfRank (rankFn d A) = (the barMult of A)` so it is provably IsKostant; then `KostantPartition d := {m : RealizableDiffArray d // IsKostant ...}` won't work because the carrier still has artifacts. 

QUESTION: Is there a THIRD route that avoids proving injectivity of truncation from scratch — e.g. transport injectivity from `diffArrayOfRank_injective` by showing truncation ∘ diffArrayOfRank-image is injective because diffArrayOfRank is recoverable from its truncation ON THE REALIZABLE SET via a cheap map (cumul reads only i≤j, so the upper-triangular truncation already determines the full diffArrayOfRank through rankFn)? Concretely: which is the lightest, and what is the minimal lemma set?
</task>

<output_contract>
1. Recommend ONE route (A, B, or a third), in 3-5 sentences, optimizing for fewest new nontrivial lemmas.
2. Give the precise `KostantPartition d` TYPE definition (Lean) you recommend.
3. List the exact lemmas/Equiv combinators needed, marking each trivial / moderate / hard, with the Mathlib name if applicable (subtypeUnivEquiv, Equiv.Set.image, subtypeEquivRight, etc.).
4. The single hardest obligation and how to discharge it cheaply.
Be concrete and Lean-specific. Do not write full proofs; give the skeleton + lemma names.
</output_contract>

<grounding_rules>
Mark any Mathlib lemma name you are not certain exists at v4.29 as "verify". Distinguish "this definitely works" from "I believe".
</grounding_rules>
