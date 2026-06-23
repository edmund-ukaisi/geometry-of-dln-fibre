<task>
I must formalise in Lean 4 + Mathlib v4.29 a self-contained "backward-greedy min-suffix realizer" over ℤ.
All math is verified true (Monte-Carlo, 0 fails). I need the CLEANEST proof ARCHITECTURE — which
characterizations / representations minimise Lean friction. I will write the Lean; I want your diagnosis
of the proof skeleton + which Mathlib idioms to lean on, NOT Lean code I paste blindly.

OBJECTS (all ℤ, nonneg, but nonneg may not even be needed):
- b : List ℤ, length n  (the "widths", NOT sorted)
- R : Multiset ℤ, card n (the "pool")
- sortedAsc : ascending sort.
- Dom b R := R.card = b.length ∧ ∀ i, (sortedAsc R)[i] ≥ (sortedAsc b.toMultiset)[i]   (pointwise domination of sorted-R over sorted-b).

ENGINE-2 (the crux, verified 0-fail on 10.7M states):
  Given Dom b R and b ≠ [], let t := b.getLast.  Then
  (i) ∃ v ∈ R, t ≤ v, and letting v := MIN such element (smallest w ∈ R with t ≤ w),
  (ii) Dom (b.dropLast) (R.erase v).
  KEY OBSERVATION I found: Dom depends only on the MULTISET of b. b.dropLast removes the VALUE t=b.getLast
  once from b's multiset; R.erase v removes v once. So ENGINE-2 is a pure MULTISET fact:
  "remove value t from b's multiset, remove min{w≥t} from R's multiset; sorted domination is preserved."

ENGINE-1: backwardGreedy b R : List ℤ by strong recursion on R.card. If b=[] return []; else
  t:=b.getLast; v:=min{w∈R: t≤w}; backwardGreedy (b.dropLast) (R.erase v) ++ [v].
  Claims given Dom b R, q := backwardGreedy b R:
   (a) (q:Multiset) = R   (b) q.length=b.length ∧ ∀ j, b[j] ≤ q[j]
   (c) MIN-SUFFIX-OPTIMALITY: ∀ p a permutation of R with ∀j b[j]≤p[j], ∀ j: ∑_{i≥j} q[i] ≤ ∑_{i≥j} p[i].
  (NOT naive pairwise exchange — that fails. Use atom: q[n-1]=min{w≥b_{n-1}} ≤ p[n-1] + ENGINE-2 + induction.)

QUESTIONS — I want concrete, decisive guidance:
1. REPRESENTATION: For Dom, is the cleanest Lean characterization (a) positional getElem on mergeSort lists,
   (b) the COUNT/filter characterization "∀ threshold τ, (R.filter (·<τ)).card ≤ (b.filter (·<τ)).card"
   [equiv to pointwise sorted domination], or (c) Mathlib's Multiset ordering / something else?
   The count form seems erase-friendly. Confirm the equivalence count-form ⟺ sorted-domination and whether
   it's the right Lean tool, OR warn me if it's a trap.
2. ENGINE-2 closure proof: give the cleanest argument in the chosen representation. In the count form:
   for threshold τ, need (R.erase v).filter(<τ).card ≤ (b.erase t).filter(<τ).card given the R/b version.
   Walk the case split on τ vs t and τ vs v (v=min{w≥t}, so all w with t≤w<v are absent from R).
   Identify the exact inequality chain. Is count-form actually clean here, or does the min-pick v break it?
3. ENGINE-1(c) min-suffix optimality: confirm the right-to-left induction works and state the induction
   hypothesis precisely (what's the statement at the (b.dropLast, R.erase v) level, and how does the atom
   q_last ≤ p_last + IH give ∑_{i≥j} q ≤ ∑_{i≥j} p for ALL j simultaneously, including j ≤ n-1?).
   The j-loop is the subtle part: suffix-sum at j = q_last + suffix-sum-of-rest at j. Spell out the splice.
4. Any Mathlib v4.29 lemmas you're confident exist for: mergeSort sorted+perm, Multiset.sort/coe_sort,
   Multiset.le_iff_count, filter card under erase, List.find? = min on sorted. (I'll verify names; just point.)
</task>

<output_contract>
Four numbered sections matching Q1-Q4. For Q1 a DECISION (which representation) + one-line why.
For Q2 the inequality chain explicitly (the τ case split). For Q3 the precise IH + the suffix-splice algebra.
For Q4 a short list of lemma-name leads. Be decisive; flag anything you're unsure is TRUE vs just plausible.
Keep under ~700 words. No Lean syntax dumps — pseudo-math is fine.
</output_contract>

<grounding_rules>
Distinguish what is mathematically certain (you can prove on paper) from Lean-API guesses (lemma names you
"think" exist). Mark the latter explicitly as "verify name". Do not invent Mathlib lemma signatures as fact.
</grounding_rules>
