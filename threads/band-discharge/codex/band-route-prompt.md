<task>
Lean 4 / Mathlib formalisation. I must discharge ONE goal (the "band"). Pick the
LEAST-friction proof route and pin its Lean encoding. I have all sub-lemmas; the
question is the GLUE, not the math (math is 0-fail verified numerically).

SETUP (all GREEN, proven):
- b : List ℤ  (widths, length L);  R : Multiset ℤ (pool, card L).
- Dom b R := (R.card = b.length) ∧ ∀ τ:ℤ, cLt R τ ≤ cLt b τ   [head-count domination]
- hDom : Dom b R   (PROVEN for my b=Mwidths, R=Ymulti).
- backwardGreedy b R : List ℤ  (right-to-left: place minimal pool elt ≥ each width).
- backwardGreedy_perm hDom : (backwardGreedy b R : Multiset ℤ) = R
- backwardGreedy_length hDom : (backwardGreedy b R).length = b.length
- backwardGreedy_ge hDom : ∀ j hj, b[j] ≤ (backwardGreedy b R)[j]
- Feasible b p := ∀ i hb hp, b[i] ≤ p[i]
- backwardGreedy_suffix_le hDom :
    ∀ p:List ℤ, (↑p)=R → Feasible b p → ∀ k, ((backwardGreedy b R).drop k).sum ≤ (p.drop k).sum
  [the greedy MINIMISES every suffix sum over all feasible perms of R]
- engine2_closure hD h : Dom b.dropLast (R.erase (pick (b.getLast h) R))  [one-step closure]
- pick t R = minimal pool value ≥ t; pick_exists/pick_mem/le_pick/pick_le available.
- qStar M i := (backwardGreedy (Mwidths M) (Ymulti M)).getD i 0   (ℕ→ℤ, junk 0 past L)
- I also have a closed-form arithmetic lemma good_floor_core :
    cAch M * aS M i ≤ Sprefix M (cAch M + 1) + (i-1)   for 1 ≤ i ≤ cAch M.

GOAL (the band), for all j : Fin L:
  (∑ i in range (j+2), Mseq M i) - (admBound M j : ℤ) ≤ ∑ i in range (j+1), qStar M i
where Mseq M i = M^i (0 past L), admBound M j = (if j=0 then min(M0,M1) else M^{j+1}).

VERIFIED REDUCTION (numerically 0-fail, 19525 cases):
Since ∑_{i<L} qStar = ∑M (total, via perm), the band ⟺ a SUFFIX bound
  suffix_{j+1}(qStar) ≤ (∑_{i=j+2}^{L} M^i) + admBound_j.
By backwardGreedy_suffix_le, suffix_{j+1}(qStar) ≤ suffix_{j+1}(p) for ANY feasible perm p.
So it suffices to EXHIBIT ONE feasible perm p (per j, different p allowed) with
  prefix_{j+1}(p) ≥ S'_{j+2} − admBound_j   (S'_n = ∑_{i<n} M^i).
The verified witness is FORWARD-MAX: left-to-right, place the LARGEST remaining pool
value that keeps the remaining Dom feasible. Its prefix bound reduces to good_floor_core.

THE FRICTION: building forward-max needs a Decidable filter {w ∈ R : t ≤ w ∧ Dom b.tail (R.erase w)}
— Dom has a ∀τ:ℤ, so it is not syntactically Decidable. Options I see:
 (A) open Classical / Classical.dec to get noncomputable Decidable (Dom ...), build forward-max recursively.
 (B) Prove the band DIRECTLY on qStar=backwardGreedy by induction on its recursion (peels the LAST
     position; the suffix form is natural for right-to-left). Avoids building a 2nd function.
 (C) Some abstract existence: "∃ feasible perm p with prefix_{j+1}(p) ≥ (the j+1 largest feasibly-
     placeable values)" proven non-constructively via a swap/exchange argument, no Decidable filter.

DEAD ENDS (verified, do NOT suggest): rank-match/ascending-pointwise witness (minimises prefix, FAILS);
"Y largest-in-front" (FAILS); monotone/descending Yvec telescopes (FAIL feasibility); suffix_le alone
is vacuous (greedy ≥ greedy).
</task>

<output_contract>
1. RANK routes A, B, C (and any 4th you see) by EXPECTED LEAN LINE-COUNT and risk, 1 line each.
2. For the WINNER: a concrete Lean proof skeleton (lemma statements + key tactic steps + which
   Mathlib lemmas), enough that I can fill it. Be concrete about the induction measure / the
   exchange step. ≤ 60 lines.
3. The single biggest gotcha that will eat time, and how to dodge it.
Keep total under ~120 lines. Concrete over prose.
</output_contract>

<grounding_rules>
You may assume the listed lemmas exist exactly as typed. Do NOT invent Mathlib lemma names you
are unsure of — if you need a lemma, say "a lemma of the form X (verify name)". Flag any step where
you are guessing the induction goes through vs. you are sure.
</grounding_rules>
