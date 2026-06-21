<task>
I am formalising in Lean 4 (Mathlib) a pure integer-combinatorics inequality. I want the
SIMPLEST PROOF STRUCTURE for a Finset.sum telescope so the Lean proof is as short and robust
as possible. Give me the cleanest induction/decomposition, NOT Lean code.

SETUP (all over ℤ, total functions g : ℤ → ℤ → ℤ with an "out of range = 0" convention realised
by support: g i j = 0 whenever i < 0 OR j > n OR i > j). Assume g i j ≥ 0 everywhere ("nonneg
triangular"). Define the second difference
    d g a e := g a e − g a (e+1) − g (a−1) e + g (a−1)(e+1).
Fix a cell (I,J) with I < J and g I J > 0 (so I ≥ 0, J ≤ n). Define the "rectangle-in-support"
family (a finite set of pairs (a,e) with 0 ≤ a ≤ I and J ≤ e ≤ n):
    A := { (a,e) | a ≤ I ∧ J ≤ e ∧ ∀ i ∈ [a,I], ∀ j ∈ [J,e], g i j > 0 }.

GOAL: prove  Σ_{(a,e) ∈ A} d g a e  ≥  g I J.

WHAT I ALREADY KNOW (verified numerically on ~300k random arrays, 0 failures):
- For fixed a, A's e-fibre is an interval [J, E(a)] (downward-closed in e), possibly empty.
- The a-fibre is nonempty exactly for a ∈ [α, I] where α = least a≤I with g i J > 0 for all i∈[a,I];
  g (α−1) J = 0.
- Inner telescope (fixed a, over e∈[J,E(a)], with q_a := E(a)+1):
    Σ_e d g a e = (g a J − g (a−1) J) − (g a q_a − g (a−1) q_a)   [since d g a e = D_a(e) − D_a(e+1),
    D_a(e) := g a e − g (a−1) e].
- Outer: Σ_{a=α}^I (g a J − g(a−1)J) telescopes to g I J − g(α−1)J = g I J.
  Remainder qterm := Σ_{a=α}^I (g(a−1)q_a − g a q_a) ≥ 0, proven by grouping [α,I] into maximal
  blocks where q_a is constant (q_a nondecreasing in a); each block [u,v] contributes g(u−1,q) ≥ 0
  because at the block top g(v,q)=0.
- The block argument is the FIDDLY part. The naive shortcut "g a q_a = 0 for all a" is FALSE
  (counterexample found).

QUESTIONS:
1. Is there a decomposition that avoids the explicit "maximal blocks" reasoning for qterm ≥ 0?
   E.g. an Abel-summation / summation-by-parts identity over the nondecreasing sequence q_a, or a
   double-counting that makes every summand manifestly ≥ 0, or a reindexing of A by a different
   parameter (e.g. by e first, or by the "staircase corner") that telescopes in one pass.
2. Specifically: is Σ_{a=α}^I (g(a−1)q_a − g a q_a) with q_a nondecreasing more cleanly handled by
   Abel/summation-by-parts: rewrite as Σ over the DISTINCT values of q (the steps of the staircase)?
   Each distinct value q taken on block [u,v] gives g(u−1,q) − g(v,q); telescoping the q-index? Does
   pairing consecutive blocks help — does it collapse to Σ over "jumps" of q?
3. Even simpler: could I prove the WHOLE thing by a single 2-D induction (on I, or on the size of the
   support rectangle), peeling one row or one column, rather than the inner+outer telescope? What is
   the cleanest induction variable and peel?
4. For Lean: which formulation minimises Finset reindexing pain — defining A as a Finset.filter over
   Finset.Icc 0 I ×ˢ Finset.Icc J n, then Finset.sum_biUnion over rows, or an explicit
   double Finset.sum Σ_{a} Σ_{e}? Flag the one most likely to fight Mathlib's Finset.sum API.

Rank the options for question 1/2/3 by Lean implementation cost (shortest, most robust first).
