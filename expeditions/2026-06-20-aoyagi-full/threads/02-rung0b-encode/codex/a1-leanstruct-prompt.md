<task>
Lean 4 / Mathlib v4.29. I need the CLEANEST Lean proof structure (not full code) for ONE lemma:
the "corridor majorization". Numerics 0-fail. The math route is settled (elementary transfers); I
need the lowest-friction Lean encoding given that Mathlib v4.29 has NO majorization/Schur API.

DEFINITIONS (in file):
  srt (n) (q : Fin n → ℤ) (i : ℕ) : ℤ := if h:i<n then q (Tuple.sort q ⟨i,h⟩) else 0   -- ascending sort, padded
  smallestK over Fin n: ∑_{i<k} srt n q i  (sum of k smallest). [I use prefix `∑ i in range k, srt n q i`]
BANKED (proven): smallestK_le_subset (n k)(hk:k≤n)(q:Fin n→ℤ)(A:Finset (Fin n))(hA:A.card=k):
  ∑_{i<k} srt n q i ≤ ∑_{j∈A} q j.   Also Tuple.sort, Tuple.monotone_sort, Equiv.sum_comp, karamata_sq.

THE LEMMA (corridor majorization, smallest-side form). Let M : Fin (L+1) → ℤ (nonneg), and let
edgeQ : Fin L → ℤ arise from an admissible T with the telescope:
  edgeQ_j = M_{j+1} + u_j − u_{j+1},  where u : ℕ → ℤ, u_0 = M_0, u_L = 0, 0 ≤ u_{j+1} ≤ min(u_j, M_{j+1}).
Define eq0 : Fin (L+1) → ℤ by eq0 = (edgeQ padded with a 0 at index L). GOAL:
  ∀ n ≤ L+1,  ∑_{i<n} srt (L+1) eq0 i  ≤  ∑_{i<n} srt (L+1) M i.     (smallestK_n eq0 ≤ smallestK_n M)

EQUIVALENT largest-side: largestK_m(edgeQ) ≥ largestK_m(M) for m ≤ L (largestK_m q = ∑q − smallestK_{len−m} q).

THE MATH PROOF (verified): build multisets v_0=M, v_{j+1} = v_j with the pair (u_j, M_{j+1}) replaced by
(u_{j+1}, edgeQ_j). Each step is an elementary transfer: same sum, one entry ↓ to u_{j+1}≤min, one ↑ to
edgeQ_j≥max. Each transfer weakly increases every largestK (equivalently weakly decreases every
smallestK). v_L = eq0 (as a multiset). So smallestK_n(eq0) ≤ smallestK_n(M).

QUESTION: what is the LOWEST-FRICTION Lean encoding? Options I see:
  (A) Multiset/Finset surgery: represent v_j as Multiset ℤ, prove an "elementary transfer ⟹ smallestK
      monotone" lemma once, then fold over j. Friction: smallestK is defined via srt on Fin n / sorted
      prefix; relating it to a Multiset and doing remove/add is awkward.
  (B) A single "elementary transfer majorization" lemma at the level of Fin (L+1)→ℤ vectors: if w' is w
      with two coordinates p<q changed to p−δ, q+δ (δ≥0, staying within order) then smallestK_n w' ≤
      smallestK_n w. Then chain L transfers, each as a vector edit. Friction: chaining L vector edits,
      tracking the intermediate vectors.
  (C) Prove largestK_m(edgeQ) ≥ largestK_m(M) by exhibiting, for each m, an explicit m-subset A of
      edge positions with ∑_A edgeQ ≥ largestK_m(M) — does the transfer structure give a CLOSED-FORM
      witness subset A_m (e.g. A_m = the m edge-positions j whose M_{j+1} is among the m largest, with
      a correction for the M_0 telescope)? [I could not find a fixed A_m; the transfer seems genuinely
      sequential. Confirm or give the witness.]
  (D) A clean "single elementary transfer ⟹ smallestK monotone" PROVED VIA smallestK_le_subset directly
      (no induction over transfers): is there a way to prove smallestK_n(eq0) ≤ smallestK_n(M) by, for
      the argmin n-subset realizing smallestK_n(eq0), MAPPING it to an n-subset of M positions with ≤
      sum? The telescope edgeQ_j = M_{j+1}+u_j−u_{j+1} might give a coordinate-wise transport.

Which option composes with the LEAST Lean friction at v4.29? Give the precise intermediate lemma(s)
and the single key inequality. If (B), give the exact statement of the elementary-transfer lemma and
how smallestK_le_subset proves it for a SINGLE transfer. If (D) works, it's preferred (no induction).
</task>

<output_contract>
1. RECOMMEND one option (A/B/C/D) with a one-line why.
2. Give the precise statement(s) of the 1-2 intermediate lemma(s) in that option.
3. For the SINGLE elementary-transfer step (or the chosen mechanism), give the KEY inequality and which
   banked engine proves it (smallestK_le_subset? a direct subset map?).
4. Flag the ONE Lean-friction risk (e.g. Tuple.sort reindexing, Multiset↔Fin, the chain bookkeeping).
Be concrete and brief. Do not invent Mathlib lemma names; if you name one, mark it "verify exists".
</output_contract>

<grounding_rules>
Distinguish forced vs inferred. The math is verified; I need the encoding with least friction at v4.29.
</grounding_rules>
