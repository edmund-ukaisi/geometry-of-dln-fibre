<task>
Lean 4 + Mathlib v4.29. I have a backward-greedy `q := backwardGreedy b R` over ℤ. Already proven
(green, no sorry): (a) q is a perm of R, (b) q.length = b.length and ∀j, b[j] ≤ q[j], plus the closure
`engine2_closure : Dom b R → b≠[] → Dom b.dropLast (R.erase v)` where v = pick (b.getLast) R = the
smallest pool element ≥ b.getLast, and `le_pick`/`pick_le` (v minimal among R-elements ≥ b.getLast).

NOW proving (c) MIN-SUFFIX-OPTIMALITY:
  ∀ p : List ℤ, (↑p : Multiset ℤ) = R → (∀ j (hj:j<b.length), b[j] ≤ p[j]) →
    ∀ j, ((backwardGreedy b R).drop j).sum ≤ (p.drop j).sum.
Right-to-left induction on b (using engine2_closure as the step). q = q' ++ [v], q' = greedy on
(b.dropLast, R.erase v). For a competitor p (nonempty, since b≠[]): u := p.getLast, p' := p.dropLast.
Feasibility gives b.getLast ≤ u (p[n-1] ≥ b[n-1]=b.getLast). u ∈ R (it's p.getLast ∈ ↑p = R), so
pick-minimality gives v ≤ u.

THE OBSTACLE (you flagged it before): IH applies to competitors for (b.dropLast, R.erase v). But
(↑p' : Multiset) = R.erase u, NOT R.erase v. When u ≠ v I must produce p♯ with (↑p♯:Multiset)=R.erase v,
feasible for b.dropLast, and control its suffix sums vs p'. Codex's earlier sketch: "replace one
occurrence of v in p' by u" — but that needs v ∈ p' (true since v ∈ R.erase u when v≠u and... need to
check multiplicity), an index k, and suffix bookkeeping splitting on k inside/outside the suffix.

I want the CLEANEST Lean encoding. Questions:

1. Is there a way to AVOID constructing the swapped list p♯ explicitly? E.g. strengthen the induction
   statement so the IH is about suffix-sums directly without needing p' to be a perm of R.erase v.
   Concretely: could I prove instead a lemma of the form
     "if (↑s : Multiset) = S, ∀j b'[j]≤s[j], Dom b' S, then ∀j greedy(b',S).drop j .sum ≤ s.drop j .sum"
   and at the TOP, rather than comparing greedy(b,R) to p, compare via: q.drop j .sum = v + q'.drop j .sum,
   p.drop j .sum = u + p'.drop j .sum, and bound q'.drop j' .sum ≤ p'.drop j' .sum where p' is a perm of
   R.erase u — handled by a SEPARATE lemma "greedy(b',R.erase v) suffix ≤ ANY feasible perm of R.erase u,
   given v≤u and v=min"? Does such a stronger statement hold and is it cleaner? Sketch its proof.

2. If the swap is unavoidable, what is the cleanest Lean construction of p♯ from p'? Options:
   (a) p♯ := p'.set k u where k = p'.idxOf v (replace first v by u);
   (b) work with multisets + an existence lemma "∃ list with these properties" via List.Perm.
   Which gives the least painful suffix-sum bookkeeping in Mathlib (List.drop, List.sum, List.set,
   List.idxOf, Perm.sum_eq)? Give the key lemma names you're confident exist (mark "verify name").

3. The suffix-sum splice: for j ≤ n-1, (q'++[v]).drop j = (q'.drop j) ++ [v], sum = q'.drop j .sum + v.
   Confirm the Mathlib lemma chain (List.drop_append / drop on concat, List.sum_append). For j = n (empty
   suffix) and j > n it's 0 ≤ 0. Spell out the j-cases so I cover them.

DECISION REQUESTED: tell me whether route (1) [stronger lemma, no explicit p♯] is viable and cleaner, or
whether I must build p♯. Pick one and give me the precise statement to prove + proof skeleton.
</task>

<output_contract>
Lead with the DECISION (route 1 stronger-lemma vs route 2 explicit-swap), one line. Then: the precise
statement(s) to prove, the induction structure, and the suffix-splice algebra. Then a short list of
Mathlib lemma-name leads (mark each "verify name" if you're not certain of the v4.29 spelling). Under
500 words. Pseudo-math fine; no long Lean dumps.
</output_contract>

<grounding_rules>
Separate what is mathematically certain (provable on paper) from Lean-API guesses. If route 1's stronger
lemma is FALSE or doesn't actually dodge the swap, say so explicitly rather than hand-wave.
</grounding_rules>
