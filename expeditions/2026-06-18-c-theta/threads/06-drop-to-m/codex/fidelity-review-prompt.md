<task>
You are a decorrelated reviewer auditing a Lean 4 formalisation of a "drop-to-m active-support
reduction" for a quadratic integer program. I want an INDEPENDENT mathematical check of two flagged
break points. Do not trust my framing; rederive.

SETUP (all integer arithmetic, no division).
- d : indices 0..N, weakly increasing (d_0 ≤ d_1 ≤ … ≤ d_N), d_i ∈ ℕ.
- e : a vector indexed 0..N-1 (0-based; call the index i, so coords e_0 … e_{N-1}), e_i ∈ ℕ,
  feasible iff ∑_{i=0}^{N-1} e_i = d_0.
- Objective Φ(e) = ∑_{i=0}^{N-1} (e_i − s_i)²  with shift  s_i = d_0 − d_{i+1}.
  (So s uses d at index i+1, i.e. the shift for 0-based coord i reads d_{i+1}.)
- A_l := (∑_{i=0}^{l} d_i) − l·d_l for l = 1..N. Pred(l) := A_l ≥ 0.
  m := max { l ≤ N : A_l ≥ 0 } (well-defined: A_1 = d_0 ≥ 0).
- S := ∑_{i=0}^{m} d_i.
- Separation lemma claimed: if m < N then  m·d_{m+1} > S, i.e. m·d_{m+1} − S ≥ 1.
- Shifted coord u_i := e_i − d_0 + d_{i+1}  (= e_i − s_i).

CLAIM UNDER REVIEW (the wall): every Φ-minimiser e* over the feasible face has
  e*_i = 0 for every 0-based i with i ≥ m   (i.e. coords m, m+1, …, N-1 all vanish).
Stronger lemma actually formalised: if a feasible e has e_k ≥ 1 for some 0-based k ≥ m, then the
single-unit transfer (j ← argmin_{i: i<m} u_i, move one unit from k to j giving e') has Φ(e') < Φ(e).

QUESTION 1 — INDEX DISCIPLINE.
The paper states "e_i = 0 for i > m" with the paper's e indexed 1..N. The Lean coord e_i is 0-based
(paper e_{i+1}). The Lean conclusion is "e_i = 0 for 0-based i ≥ m" and the transfer source
condition is "k ≥ m (0-based)", target "j < m (0-based)".
(a) Is the 0-based threshold "i ≥ m" the correct translation of paper "i > m" (paper index 1-based)?
    Show the index arithmetic. Is there an off-by-one? Is the boundary coordinate (0-based i = m,
    paper index m+1) correctly DROPPED (forced to 0) rather than kept?
(b) Is "j < m" disjoint from "k ≥ m", so j ≠ k always holds? Is the argmin set {i : i < m} nonempty
    (the lemma asserts m ≥ 1)?

QUESTION 2 — THE min-≤-average INTEGER STEP and the gap u_k − u_j ≥ 2.
The formalisation derives u_k − u_j ≥ 2 entirely in ℤ as follows. Verify each step is valid integer
reasoning (NOT requiring division / rounding), and that the final ≥ 2 is correctly extracted:
  (i)   m·u_j ≤ ∑_{i: i<m} u_i      [min over m terms ≤ sum, via card_nsmul_le_sum, m = #{i<m}].
  (ii)  ∑_{i<m} u_i = (∑_{i<m} e_i) + (S − d_0) − m·d_0   [since ∑_{i<m} d_{i+1} = d_1+…+d_m = S−d_0].
  (iii) ∑_{i<m} e_i ≤ d_0           [e ≥ 0 and ∑_{all i} e_i = d_0].
  ⟹    m·u_j ≤ S − m·d_0.
  (iv)  u_k ≥ 1 − d_0 + d_{m+1}      [e_k ≥ 1; d_{k+1} ≥ d_{m+1} since k ≥ m ⟹ k+1 ≥ m+1].
  ⟹    m·u_k ≥ m·(1 − d_0 + d_{m+1}).
  (v)   combine with separation (m·d_{m+1} − S ≥ 1):
        m·(u_k − u_j) ≥ m·(1 − d_0 + d_{m+1}) − (S − m·d_0) = m + (m·d_{m+1} − S) ≥ m + 1.
  (vi)  from m·(u_k − u_j) ≥ m+1 and m ≥ 1, conclude u_k − u_j ≥ 2 (integers).
Then Φ(e') − Φ(e) = 2(u_j − u_k + 1) ≤ 2(−1) = −2 < 0.
Specifically scrutinise step (vi): does m·X ≥ m+1 with m ≥ 1 and X ∈ ℤ really force X ≥ 2? (Check
X = 1: m·1 = m, is m ≥ m+1? No. So X = 1 excluded. X ≤ 1 ⟹ m·X ≤ m < m+1, contradiction. Confirm.)
Also confirm step (i): is "min of m terms ≤ (1/m)·sum", multiplied to "m·min ≤ sum", a valid integer
statement with NO rounding error introduced?

Also flag: does the separation feed in with the SAME d_{m+1} as appears in u_k's lower bound (iv)?
I.e. is there a hidden index mismatch between S = ∑_{0..m} d_i (reads d_0..d_m) and the d_{m+1} in
both separation and the u_k bound?
</task>

<output_contract>
Two sections, "Q1 index discipline" and "Q2 integer gap". For each: VALID / INVALID / off-by-one
found, with the exact index arithmetic shown. For Q2 step (vi) give the explicit integer argument.
End with a one-line verdict: does the wall lemma (e_i=0 for 0-based i≥m) follow, with no off-by-one
and no division artefact? Be terse.
</output_contract>

<grounding_rules>
Rederive the index arithmetic yourself; do not accept my "i ≥ m is correct" assertion without
checking. Mark any step you cannot verify as "cannot confirm" rather than agreeing. Distinguish a
genuine mathematical error from a mere naming/convention difference.
</grounding_rules>
