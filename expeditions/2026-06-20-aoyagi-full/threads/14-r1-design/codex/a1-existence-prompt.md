<task>
We need a CONSTRUCTIVE EXISTENCE proof, formalizable in Lean 4 + Mathlib, of the following
combinatorial-feasibility fact. A multiset of L nonnegative integers must be arranged into an
ordered tuple subject to per-position lower bounds AND a two-sided prefix-sum corridor. We want
the cleanest certificate (a deterministic construction + an inductively-CLOSED invariant, OR a
non-greedy existence argument via a known feasibility theorem) that a fresh formaliser can transcribe.

THE EXACT PROBLEM. Given:
- L >= 1, and widths w_0,...,w_{L-1} >= 0 (these are M^1,...,M^L, the "next-layer" widths).
- S_n := M^0 + M^1 + ... + M^n  (inclusive prefix sums of the full width vector M of length L+1),
  so S_0 = M^0 and S_L = total. Note w_j = M^{j+1} = S_{j+1} - S_j.
- A multiset Y of L nonnegative integers (its construction is in <grounding_rules>).
- An "admBound" sequence: admBound_0 = min(M^0, M^1); admBound_j = M^{j+1} for j >= 1.

Find a tuple q = (q_0,...,q_{L-1}) that is a PERMUTATION of Y and satisfies, writing P_n = q_0+...+q_{n-1}:
  (L)    q_j >= M^{j+1}                       for all j in 0..L-1   [positional lower bounds]
  (U)    P_n <= S_n                            for all n in 1..L     [upper corridor]
  (Ladm) P_n >= S_n - admBound_{n-1}           for all n in 1..L     [lower corridor]
  (T)    P_L = S_L                             [total = sum of all widths >= 1]

DELIVERABLE. Either:
(A) A deterministic construction (e.g. a forward greedy that picks, at each position, a specific
    element of the remaining multiset) TOGETHER WITH a loop invariant that is (i) true initially,
    (ii) preserved by one step, (iii) strong enough to guarantee the per-step pick exists (window
    non-empty) AND that the final tuple satisfies (L)(U)(Ladm)(T). The invariant must be a STATEMENT
    ABOUT THE CURRENT STATE (remaining multiset + running prefix) that is genuinely inductively closed
    — not merely "true on reachable states". State it precisely.
(B) A NON-GREEDY existence argument: identify the exact known theorem (Gale's transportation
    feasibility / Gale-Ryser / Hall's marriage / a flow/circulation feasibility / a majorization-implies-
    arrangement result) whose hypotheses are met here, give the precise feasibility condition in terms of
    the data above, and sketch how to discharge it constructively in Lean (Mathlib has Hall's theorem
    `Finset.all_card_le_biUnion_card_iff_exists_injective`; it does NOT have Gale-Ryser or transportation
    feasibility as a named theorem at v4.29).
</task>

<output_contract>
1. VERDICT: which route (A construction+invariant, or B named theorem) gives the cleanest Lean proof,
   and WHY. If (A), give the explicit pick rule and the EXACT invariant (a closed predicate on
   (remaining-multiset, running-prefix-index n, current prefix-sum P_n) — or whatever state you choose),
   and PROVE (sketch) it is inductively closed and forces window-non-emptiness.
2. If you propose a greedy: state precisely WHY it does not hit the controller's failure mode (an
   abstract invariant that holds on a non-reachable state but breaks one step later). The known failure:
   "conservation (P_n = S_n - u_n with u_n the running level) + small-end caps (every k-smallest of
   remaining <= corresponding prefix cap)" is NOT inductively closed — counterexample remaining=[2,2,3,5],
   running-level u=4, remaining-widths=[4,0,0,4], cap=3: aggregate small-end caps hold but two slots each
   need a value >= 4 while only ONE remaining value is >= 4 (a HIGH-end Hall failure the small-end caps
   don't see). Your invariant MUST also control the high end.
3. State the exact FEASIBILITY CONDITION (the two-sided majorization or Gale condition) you rely on,
   in the data above, and which direction needs proving vs. is automatic.
4. Flag any inference vs. fact. Do NOT paste long Lean code; give the math certificate + the lemma shapes.
</output_contract>

<grounding_rules>
- This is the UPPER-bound (achiever) half of an RLCT learning-coefficient theorem. The lower bound is
  already proven; we only need ONE feasible q at the target value, so existence of a feasible permutation
  of Y suffices — no optimisation.
- The multiset Y is built from M as follows. Sort M ascending to a (a_0<=...<=a_L). The "achiever" is the
  largest c in {1..L} with the cumulative-ceiling predicate good(c): for all 1<=i<=c, i*a_i <= S_i + i - 1
  (where here S_i = a_0+...+a_i on the SORTED a). Let P = a_0+...+a_c (sum of the c+1 smallest widths) and
  tail = (a_{c+1},...,a_L) (the L-c largest). Then Y = balancedSplit(P, c) ⊎ tail, where balancedSplit(P,c)
  is the c integers floor(P/c) or ceil(P/c) summing to P (r copies of b+1 and c-r of b, b=P/c, r=P%c).
  So Y has exactly L elements.
- VERIFIED EXACT FACTS (Python, exhaustive over widths 0..3, L<=4, 1360 cases; widths 0..4 L<=5 for the
  majorizations, 19525 cases): (i) a feasible q ALWAYS exists (0 failures). (ii) existence is EQUIVALENT
  to the two-sided majorization: for all k, smallestK_k(Y) <= S_k  AND  largestK_k(Y) >= largestK_k(widths)
  (0 mismatches vs brute-force existence). (iii) BOTH majorizations hold for the achiever Y unconditionally
  (0 failures): the small-end one is an already-proven lemma; the big-end one is its dual. (iv) The lower
  corridor (Ladm) is NOT implied by (L)+(U) for an arbitrary placement — the deterministic "assign largest
  Y to largest-width slot" placement violates (Ladm) in 459/1360 cases (always recoverable by a different
  permutation). (v) "smallest-in-window greedy" with the local conservation+small-end invariant is correct
  on reachable states but the invariant is not inductively closed (the controller's counterexample above).
- smallestK_k(X) = sum of k smallest elements of multiset X; largestK_k(X) = sum of k largest.
- Lean context: q,Y are Fin L -> Int (or Multiset Int); Mathlib has Tuple.sort, Finset.sum, Multiset.erase,
  Hall (`Finset.all_card_le_biUnion_card_iff_exists_injective`), Finset.exists_... but NO Gale-Ryser /
  transportation-feasibility / Schur-convexity / "sum of k smallest" named API. Strong induction on
  |remaining multiset| is available and clean.
- Withhold judgement on which route I prefer — give your independent verdict.
</grounding_rules>
