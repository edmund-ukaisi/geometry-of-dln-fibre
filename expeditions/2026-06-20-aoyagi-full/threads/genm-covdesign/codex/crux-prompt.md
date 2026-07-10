<task>
I am checking the recursion structure of an RLCT finiteness proof (deep linear networks, Aoyagi). Please
work out ONE structural question independently and exactly; do not defer to a "standard" reduction.

SETUP. Chain of matrix factors `M = (m_0, m_1, …, m_L)`. `A_0` is `m_0×m_1` (leading), `A_1,…,A_{L-1}`
are the tail (`A_i : m_i×m_{i+1}`), `P = A_1···A_{L-1}` is `m_1×m_L`. Loss `frobSq(A_0 P) = ‖A_0 P‖_F^2`.
All factors range over unit boxes. Fix corank `q ≥ 1` and a `q×q` pivot minor `(ρ,κ)` of `P`; the CHART
is `{P[ρ,κ] invertible}`. We want `J = ∫_{chart} ∫_{A_0 box} frobSq(A_0 P)^{-c'} dA_0 dA'` finite for
`c' < ½·minAdm(M)`.

The STRONG INDUCTION HYPOTHESIS available is the finiteness of the box integral of the REDUCED chain
`redTail = (m_1−q, …, m_L−q)` — the tail widths each dropped by `q`. redTail has ONE FEWER FACTOR than
the full chain M (it is a tail). The induction is on the NUMBER OF FACTORS (arity): the IH gives
`∫_{box} frobSq(Y_1···Y_{L-1})^{-s} dY < ∞` for all `s < ½·minAdm(redTail)`, for chains with fewer
factors than M.

THE QUESTION. Peel the `A_0` integral on the chart. Take the corank block split of `P`:
`P = [[B, E],[C, D]]`, `B = P[ρ,κ]` invertible; and split `A_0`'s columns to match `P`'s rows:
`A_0 = [X | W]`, `X` is `m_0×q` (pivot columns), `W` is `m_0×(m_1−q)` (non-pivot columns).

Work out EXACTLY:
1. After the measure-preserving shear that block-triangularises `P` (Schur complement `Z = D − C B^{-1} E`,
   the reduced quotient), what is the exact form of `frobSq(A_0 P)` in terms of `X`, `W`, the pivot rows
   `[B E]`, and `Z`? Is there a residual term coupling `W` (the non-pivot columns of `A_0`) with `Z`?
2. Peel the `X` (pivot, `m_0 q`-dim Morse) block via the whole-space Morse bound
   `∫_{ℝ^d}(x^⊤ Φ x + w)^{-c'} = (det Φ)^{-1/2}·C·w^{-(c'-d/2)}` (`c' > d/2`). What is `Φ`, what pivot
   determinant factor appears, and what is the residual core `w` — is it `‖W·Z‖²`?
3. If the residual is `∫_{W box} ‖W·Z‖^{-2s} dW` (`s = c'−m_0q/2`): recognise `W·Z = W·Y_1···Y_{L-1}`.
   What chain is this the front-integral of? How many FACTORS does that chain have, compared to M? Is it
   the SAME arity as M, or smaller? Does the arity-based IH (on redTail, fewer factors) cover it, or is
   it a same-arity sub-problem the arity induction does NOT reach?
4. If it is a same-arity sub-problem: is the finiteness recursion still well-founded under a DIFFERENT
   induction measure (e.g. total width `Σ m_i`, or tail-width-sum)? Compute `Σ`-width of that chain vs M.
</task>

<output_contract>
For each of 1–4: the exact algebra / count, PROVEN not asserted. In particular settle 3 sharply: does
the `A_0` integral reduce the per-chart problem to the SMALLER-arity redTail IH, or to a SAME-arity
`(m_0, redTail)` sub-problem? And 4: name the well-founded measure that makes the recursion close (if any),
with the exact width comparison.
</output_contract>

<grounding_rules>
Exact only. Distinguish PROVEN from CONJECTURE. If the arity induction genuinely cannot close (the
non-pivot `A_0` columns force a same-arity sub-problem), say so explicitly and name what induction measure
would fix it — this is the decision I need.
</grounding_rules>
