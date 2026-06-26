<task>
Lean 4 / Mathlib v4.29 formalisation. I have isolated the lower-bound majorization into two sharp
sub-lemmas (both verified 0-fail, L≤4). I need the cleanest ELEMENTARY proof architecture for each,
using ONLY the corridor facts + one banked engine. NO Mathlib order-statistics API exists.

SETUP. M : Fin (L+1) → ℕ, L ≥ 1, a = sort M ascending, S_n = a_0+...+a_n (SORTED prefix sums).
Achiever c = largest c∈{1..L} with `good`. P = S_c, b = P/c, r = P%c (so b,r from balanced split of
the c+1 SMALLEST widths). For T ∈ Adm M, edgeQ : Fin L → ℤ (all values ≥ 0). Banked facts:

CORRIDOR (proven, original/positional order): with S'_n = M_0+...+M_n (UNSORTED prefix),
  (C1) edgeQ_j ≥ M_{j+1} ≥ 0  (each edge ≥ its width).
  (C2) ∑_{j<n} edgeQ_j = S'_n − u_n,  where 0 ≤ u_n ≤ M_n and u antitone, u_0=M_0, u_L=0.
       Hence S'_{n−1} ≤ ∑_{j<n} edgeQ_j ≤ S'_n  (positional prefix corridor).
  (C3) ∑_{j<L} edgeQ_j = ∑ M = ∑ a (total).

BANKED ENGINE (proven):
  smallestK_le_subset (n k) (hk:k≤n) (q:Fin n→ℤ) (A:Finset (Fin n)) (hA:A.card=k):
     smallestK k q ≤ ∑_{j∈A} q j      [smallestK k q := ∑_{i<k} srt(q) i, sum of k SMALLEST entries]
  balancedSplit_min, balancedSplit_sq_int.
  Also: smallestK is MONOTONE under restriction — for B ⊇ (set of size ≥ k), smallestK over a SUBSET
        is ≥ smallestK over the whole (fewer small values available). [I can prove this.]

THE TWO SUB-LEMMAS TO PROVE (smallestK over the FULL Fin L edgeQ):
  (H4) for c ≤ n ≤ L:  smallestK n edgeQ ≤ S_n   (SORTED prefix sum; n smallest edge values).
  (H5) for 0 ≤ k ≤ c:  smallestK k edgeQ ≤ k*b + max(0, k+r−c).

CRUX DIFFICULTY (Codex flagged this earlier): the corridor (C2) is in ORIGINAL/positional order,
but H4/H5's RHS (S_n, the balanced prefix) are SORTED-width data. For UNSORTED M the positional
prefix ∑_{j<n}edgeQ ≤ S'_n is NOT ≤ S_n (verified: fails ~32% of the time). So I CANNOT use "first n
positions" as the witness subset for smallestK_le_subset. I need the RIGHT M-determined witness
subset A_n (a set of positions), OR a different argument.

KEY ADDITIONAL VERIFIED FACTS (0-fail) that might be the bridge:
  (F1) smallestK_c edgeQ ≤ S_c = P.  (the c smallest edges sum to ≤ the c+1 smallest widths' total).
  (F2) H4 and H5 BOTH hold; H5's RHS = prefix_k(srt(balancedSplit P c)) (closed form k*b+max(0,k+r−c)).

QUESTIONS:
1. For H4 (smallestK_n edgeQ ≤ S_n, n ≥ c): what M-determined n-subset A_n of positions {0..L-1}
   has ∑_{A_n} edgeQ ≤ S_n for every corridor-edgeQ, AND is provable from (C1)-(C3)? Is there a
   recursive/structural choice (e.g. tied to where M's largest widths sit)? Or does H4 follow from a
   SUM-OF-TWO-PARTS argument: smallestK_n = (total) − (largestK_{L−n}), and largestK_{L−n}(edgeQ) ≥
   ∑ of the L−n largest widths, giving smallestK_n ≤ ∑M − (largest L−n widths) = S_n? CHECK this:
   ∑M − S_n = a_{n+1}+...+a_L = the (L−n) LARGEST widths; and largestK_{L−n}(edgeQ) ≥ those? Since
   edgeQ_j ≥ M_{j+1} (C1) and there are L widths M_1..M_L (NOT M_0)... does largestK_{L−n}(edgeQ) ≥
   sum of (L−n) largest of {M_1,...,M_L}? And is sum of (L−n) largest of {M_1..M_L} ≥ a_{n+1}+..+a_L
   (the L−n largest of ALL L+1 widths incl M_0)? [This is the candidate clean route: complement +
   edgeQ_j ≥ M_{j+1}. Tell me if it composes or where it breaks — note {M_1..M_L} EXCLUDES M_0, so
   the largest L−n of {M_1..M_L} vs largest L−n of {M_0..M_L} differ; does it still dominate?]

2. For H5 (smallestK_k edgeQ ≤ k*b+max(0,k+r−c), k ≤ c): Plan = restrict edgeQ to a c-subset B with
   ∑_B edgeQ ≤ P=S_c (then smallestK_k over B ≤ balanced-prefix by Step B/balancedSplit maximality,
   and smallestK_k full ≤ smallestK_k over B by restriction-monotonicity). So I need a c-subset B
   with ∑_B edgeQ ≤ S_c. F1 says smallestK_c edgeQ ≤ S_c — so B = the c smallest-edge positions
   works (∑_B = smallestK_c ≤ S_c). Does this compose? (smallestK_k over the c smallest = smallestK_k
   over full when k ≤ c, since the k smallest are among the c smallest — so it's an EQUALITY, even
   cleaner.) Confirm: smallestK_k(edgeQ) = smallestK_k(edgeQ restricted to its c smallest), and Step B
   gives ≤ balanced prefix. So H5 reduces to F1 (smallestK_c edgeQ ≤ S_c) + Step B. Right?

3. So BOTH H4 and H5 may reduce to: (a) F1-type complement bounds (largestK edgeQ ≥ largest widths),
   and (b) Step B (balanced maximality). Is the complement identity smallestK_n(q) = ∑q − largestK_{L−n}(q)
   the unifying clean tool? Give the cleanest 2-3 lemma decomposition covering BOTH H4 and H5.
</task>

<output_contract>
1. VERDICT on the complement route for H4 (does largestK_{L−n}(edgeQ) ≥ a_{n+1}+...+a_L compose from
   edgeQ_j ≥ M_{j+1}? where does M_0's exclusion bite, and is it fatal or handled?). Mark forced vs needs-check.
2. VERDICT on the H5 reduction to F1 + Step B (is the restriction-to-c-smallest equality right?).
3. The cleanest unified lemma list (≤4 lemmas, with statements) covering H4+H5. Note: I want to MINIMISE
   from-scratch order-statistics; lean on smallestK_le_subset + a complement identity + Step B.
4. ONE-LINE: is F1 (smallestK_c edgeQ ≤ S_c) itself the crux, and does IT follow from the corridor, or
   is IT the residual design gap? If F1 needs the achiever's `good c` property, say so.
</output_contract>

<grounding_rules>
Distinguish forced-from-(C1,C2,C3,engine) vs needs-check/inference. Do not invent Mathlib names.
The numerics are verified; tell me if a step is true-but-unprovable-from-listed-facts (a real gap).
</grounding_rules>
