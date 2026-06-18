<task>
Lean 4 + Mathlib v4.29. I need the cleanest tactic route to prove ONE strict-decrease inequality.

CONTEXT (all committed/proved):
- `codimBil N A B := ∑ i ∈ Finset.Icc (1:ℤ) N, ∑ u ∈ Icc i N, ∑ j ∈ Icc u N, ∑ v ∈ Icc j N,
     A (i-1) (j-1) * B u v`   (A B : ℤ→ℤ→ℤ)
- `codimForm N M = codimBil N M M`.
- `codimForm_add : codimForm N (A+B) = codimForm N A + codimBil N A B + codimBil N B A + codimForm N B`. [proved]
- `concatDelta a b c d' : ℤ→ℤ→ℤ := fun α β ↦ (if α=a ∧ β=d' then 1 else 0) - (if α=a ∧ β=b then 1 else 0)
     - (if α=c ∧ β=d' then 1 else 0)`   (a,b,c,d' : Fin(N+1) cast to ℤ; c = b+1).
- `extendℤ_concatMove : extendℤ (concatMove m a b c d') = extendℤ m + concatDelta a b c d'`. [proved]
  So with M := extendℤ m: `codimForm (extendℤ (concatMove ...)) = codimForm M + codimBil M δ + codimBil δ M + codimForm δ`
  where δ = concatDelta.

GOAL: prove `codimForm N (extendℤ (concatMove m a b c d')) ≤ codimForm N (extendℤ m) - 1`,
i.e. the correction `codimBil M δ + codimBil δ M + codimForm δ ≤ -1`,
GIVEN: a ≤ b, (c:ℕ)=b+1, c ≤ d', 1 ≤ a (interior left), m(a,b) ≥ 1, m(c,d') ≥ 1, and `extendℤ m` ≥ 0 entrywise
(it is a ℕ-array cast).

EXACT correction (verified symbolic, sympy, all small N), with M_P = m-multiplicity at interval P:
  correction = 1 − Σ_{P ∈ R} κ_P · M_P
where R is a finite region of intervals, every κ_P ≥ 0, AND the two source intervals (a,b) and (c,d')=(b+1,d')
are in R with κ ≥ 1. E.g. N=4 [1,2]+[3,3]→[1,3]: corr = 1 − m(1,2) − m(2,2) − m(2,3) − m(3,3).
So correction ≤ 1 − M(a,b) − M(c,d') ≤ 1 − 1 − 1 = −1.

The difficulty: collapsing `codimBil M δ` and `codimBil δ M` — δ is supported at 3 points, so each is a
finite linear functional of M, but the 4-fold ℤ-Icc sum must be reduced. And `codimForm δ` is a 3×3 constant.

<output_contract>
1. The cleanest Lean route to the bound `correction ≤ -1` WITHOUT computing the full exact κ_P formula.
   Specifically: can I avoid the exact region R by bounding? E.g. prove
   `codimBil M δ ≤ -M(a,b)` and `codimBil δ M ≤ -M(c,d')` and `codimForm δ ≤ 1` separately (or some split
   that isolates the two −1's and a +1)? Give the cleanest such SPLIT and which Mathlib lemmas collapse each.
2. To collapse `codimBil A δ` (δ supported at Q ∈ {Q1,Q2,Q3}): the inner `∑ v ∈ Icc j N, A(i-1)(j-1) * δ u v`.
   δ u v = sum of 3 indicators on (u,v). Recommended: `Finset.sum_eq_single_of_mem` per indicator, or rewrite
   δ as a 3-term sum and use `Finset.sum_add_distrib` / `mul_add`? Name the v4.29 lemmas. Flag [SURE]/[GUESS].
3. For `codimBil δ A` the δ is in the (i-1,j-1) slot — the OUTER indices. How to collapse i,j to the two
   values (a+1,b+1),(a+1,d'+1),(c+1,d'+1)? (Reindex shift i-1=α.) Cleanest approach?
4. Is it cleaner to NOT use codimForm_add, and instead prove the inequality
   `codimForm (extendℤ (concatMove ...)) ≤ codimForm (extendℤ m) - 1` by a direct `Finset.sum_le_sum` /
   termwise comparison on the two 4-fold sums? Or is the additive δ-expansion genuinely cleaner?
   Give your single recommended path + a line-count estimate (NO wall-clock) + subtask list.
</output_contract>
<grounding_rules>
Mark lemma names [SURE]/[GUESS] for v4.29. Don't invent. If the honest answer is "you must compute the
exact region R", say so and give the most mechanical way to do it.
</grounding_rules>
