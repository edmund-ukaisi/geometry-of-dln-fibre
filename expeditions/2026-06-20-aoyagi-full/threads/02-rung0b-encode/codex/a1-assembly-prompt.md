<task>
Lean 4 + Mathlib v4.29 formalization. I have BANKED (proven, green) these two lemmas toward
`lambdaCore_eq_clean`:

  -- Karamata for squares, ascending-prefix form, over ℤ (range-indexed):
  karamata_sq (n) (x y : ℕ→ℤ)
    (hmono : ∀ i, i+1<n → y i ≤ y (i+1))            -- y ascending
    (htot  : ∑_{i<n} x i = ∑_{i<n} y i)
    (hpre  : ∀ k≤n, ∑_{i<k} x i ≤ ∑_{i<k} y i)
    : ∑_{i<n} (y i)^2 ≤ ∑_{i<n} (x i)^2

  -- Edge identity (CERTAIN): with Useq/Mseq/edgeQ : ℕ→ℤ functions,
  --   Useq M T 0 = M0, Useq M T (j+1) = T_j, Mseq M i = M_i, edgeQ M T j = Mseq(j+1)+Useq j - Useq(j+1)
  edge_identity (M T) (hL:1≤L) (hlast: last T = 0)
    : 2 * Mval M T = (∑_{j<L} (edgeQ M T j)^2) - ∑_{i<L+1} (Mseq M i)^2

  -- also have prefix_edgeQ: ∑_{j<n} edgeQ = (∑_{i<n+1} Mseq i) - Mseq 0 + (Useq 0 - Useq n).

The numerically-VERIFIED facts (0 failures, exhaustive L<=4):
  - QFeasible(M,q) := (∑q = ∑M) AND (∀j, M_{j+1} ≤ q_j) AND (∀ 1≤n≤L, S_{n-1} ≤ ∑_{j<n} q_j ≤ S_n),
    S_n = M_0+...+M_n.  Adm M  ↔  QFeasible M (edgeQ M T)  (bijection both ways, roundtrip verified).
  - The minimum of ∑_{j<L} q_j^2 over QFeasible q equals
        minSumSq(M) = (balancedSplit sum-of-squares of P_c into c parts) + ∑_{i=c+1}^{L} a_i^2,
    where a = sort(M) ascending, c = cstar(M) (largest c in 1..L with cumulative ceiling predicate),
    P_c = a_0+...+a_c, and balancedSplit-sum-of-squares = c*(P_c/c)^2 + (P_c%c)*(2*(P_c/c)+1).
  - The target multiset Y = {β_0..β_{c-1}} ∪ {a_{c+1}..a_L} where β = balanced split of P_c into c parts.
  - Karamata hypothesis VERIFIED: for any QFeasible q, with x = sort(q) ascending and y = sort(Y)
    ascending: equal totals and ∀k, ∑_{i<k} x_i ≤ ∑_{i<k} y_i. (So karamata_sq gives ∑Y^2 ≤ ∑q^2.)
  - 2*cleanCore(c, sortedSmallest M c) = minSumSq - ∑M^2 = Vstar (pure arithmetic via balancedSplit_sq_int).
  - cstar arithmetic verified: good c ⟹ a_{i+1} ≤ β_i (i<c); maximality ⟹ β_{c-1} < a_{c+1} when c<L.

FROZEN goal: `∃ c≤L, 1≤c ∧ lambdaCore M = cleanCore c (sortedSmallest M c hc)`,
  lambdaCore M = (1/2)·(Adm M).inf' (Mval M).  Strategy: pick c=cstar; show
  2·lambdaCore M = minMval = minSumSq - ∑M^2 = 2·cleanCore(cstar, sortedSmallest).

## The two remaining hard bridges — I need the LEAST-FRICTION Lean recipe for each

BRIDGE A (LOWER bound): ∀ T ∈ Adm M, minSumSq(M) ≤ ∑_{j<L} (edgeQ M T j)^2.
  Plan: from Adm derive QFeasible (positional prefix bounds on edgeQ). Then need to feed karamata_sq.
  karamata_sq needs x SORTED ASCENDING with prefix-domination over the sorted target Y. So I must
  (a) sort edgeQ : Fin L → ℤ (it is positional, not sorted), keeping ∑(edgeQ)^2 = ∑(sorted edgeQ)^2,
  (b) prove the sorted-edgeQ prefix sums are ≤ sorted-Y prefix sums.
  THE PAIN: step (b) — relating the sorted prefix sums of edgeQ to the POSITIONAL QFeasible bounds
  (S_{n-1} ≤ ∑_{j<n} edgeQ_j ≤ S_n) and to the bound edgeQ_j ≥ M_{j+1}. Is there a clean Mathlib
  route? Specifically: is the prefix-sum-of-smallest-k ≤ any-positional-prefix-sum-of-k usable, plus
  the lower bound q_j ≥ M_{j+1}? Or is there a way to AVOID sorting edgeQ by stating karamata_sq
  differently (e.g. a version where x need not be sorted, only y, using rearrangement)?

BRIDGE B (UPPER bound / achiever): construct T* ∈ Adm M with ∑(edgeQ M T*)^2 = minSumSq, then
  lambdaCore M ≤ ½ Mval M T* (Finset.inf'_le) = ½(minSumSq - ∑M^2) = cleanCore(cstar, sortedSmallest).
  On SORTED M the achiever q* = (ascending β)++(a tail) is explicit; but Adm M is on the ORIGINAL
  (unsorted) M. Two sub-options: (B1) prove lambdaCore M = lambdaCore (sort M) first [needs Adm↔Adm
  perm bijection — HARD], then work on sorted M; (B2) greedily place Y into original positions
  (Codex's earlier greedy). Which is less Lean friction? And how to match the achiever's edge multiset
  to `sortedSmallest M c` for cleanCore (via cleanCore_perm)?

## What I need
1. BRIDGE A: the single cleanest Lean tactic-route to get from QFeasible (positional prefix bounds)
   to the karamata_sq hypotheses. If sorting edgeQ is unavoidable, the exact Mathlib lemmas for
   "sorted prefix sum ≤ positional prefix sum" (Tuple.sort, Finset, monovariant). If there's a way to
   restate the lower bound to AVOID sorting edgeQ, give it.
2. BRIDGE B: B1 vs B2 verdict (Lean friction), and the achiever construction with least casts.
3. A REALISTIC line-count estimate for each bridge and a recommendation: is the full close ~150-250
   more lines, or should I bank the lower bound only / a clean sub-lemma and stop? (This theorem is
   OFF the headline critical path.)
</task>

<output_contract>
1. BRIDGE A recipe: cleanest route, exact Mathlib lemma names if you know them, or the restatement
   that avoids sorting edgeQ. Flag CERTAIN vs INFERRED.
2. BRIDGE B verdict: B1 vs B2 + achiever construction sketch + multiset match.
3. Line-count estimate per bridge + STOP/CONTINUE recommendation given it's off critical path.
Be concrete and tight. Flag any Mathlib lemma name you are not sure exists.
</output_contract>

<grounding_rules>
All numeric facts above are exhaustively verified by me; treat as TRUE. For any Mathlib lemma you
cite, flag whether you are CERTAIN it exists at v4.29 or INFERRING — I will verify before using.
Do not assert a tactic will close a goal as fact; mark it as a plan to try.
</grounding_rules>
