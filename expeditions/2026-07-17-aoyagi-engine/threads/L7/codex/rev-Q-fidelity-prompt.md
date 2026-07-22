<task>
I am fidelity-reviewing a Lean 4 lemma against a pen-and-paper certificate. I want an INDEPENDENT
derivation of the correct statement, so I can check whether the Lean matches. Do NOT trust my framing;
derive it yourself.

SETTING. Ambient space is (Fin D → ℝ) with the SUP norm (so `Metric.ball 0 R = {x | ∀ j, |x_j| < R}`,
`Metric.closedBall 0 ρ = {x | ∀ j, |x_j| ≤ ρ}`). Fix a nonempty finite center S ⊆ Fin D. For a pivot
p ∈ S define the block blow-up map
    blockBlowupMap S p (w) : j ↦  w_p              if j = p
                                  w_p · w_j        if j ∈ S, j ≠ p
                                  w_j              if j ∉ S   (spectator, passed through).

CERTIFICATE CLAIM (call it Q). "The open unit cube around 0 is covered by the union over pivots p ∈ S
of the images of blockBlowupMap S p on the closed unit cube; spectators passed through", i.e.
    ball 0 1  ⊆  ⋃_{p ∈ S}  blockBlowupMap S p '' (closedBall 0 1).
The stated routing: at target x, pick pivot p = argmax_{q ∈ S} |x_q|; lift w_p = x_p, w_q = x_q / x_p
(q ∈ S\{p}), spectators w_j = x_j; the S-ratios are ≤ 1 by maximality.

THE LEAN GENERALISES to arbitrary radius R > 0 with SOURCE BOX radius (max R 1):
    ball 0 R  ⊆  ⋃_{p ∈ S}  blockBlowupMap S p '' (closedBall 0 (max R 1)).

FOUR QUESTIONS.
1. Is Q TRUE exactly as stated (with the open ball on the left, closed unit cube source)? Derive the
   witness for an arbitrary x with |x_j| < 1 ∀ j, including the degenerate x_p = 0 (max over S is 0) case
   and the singleton |S| = 1 case. Confirm the ratio bound and the pivot/spectator bounds.
2. For the general-radius form: is (max R 1) the CORRECT and TIGHT source-box radius? I.e. is a smaller
   radius (say R, or 1) provably insufficient for some R, and does (max R 1) always suffice? Give the
   scale of each coordinate of the witness (pivot, center-ratio, spectator) as a function of R.
3. Is S.Nonempty the ONLY hypothesis Q needs (besides R > 0 for the radius form)? Are there hidden side
   conditions (e.g. does it secretly need p ∈ S baked as a hypothesis, 2 ≤ D, D ≠ 0, or a
   distinctness/tie-breaking assumption)? Is the statement vacuous at D = 0?
4. Does S = univ recover the full-ambient origin blow-up cover `ball 0 1 ⊆ ⋃ i, blowupMap i '' closedBall 0 1`
   where blowupMap i w j = (if j = i then w_i else w_i · w_j)? Any subtlety in that recovery?
</task>

<output_contract>
Four numbered answers, each ≤ 8 lines. For each, state your VERDICT first (TRUE / FALSE / TIGHT / NOT
TIGHT / recovers / does-not-recover), then the derivation. If you find the certificate routing or the
(max R 1) box WRONG, give the explicit counterexample x (coordinates as functions of R and ε).
End with a one-line overall: does the Lean statement (open ball LHS, closedBall (max R 1) source,
⋃ over p ∈ S, only S.Nonempty + R>0) faithfully capture Q?
</output_contract>

<grounding_rules>
This is pure elementary real analysis — derive everything from scratch. Mark any step you are UNSURE of
as [unsure]. Do not assume my framing is correct; if the routing fails at an edge case, say so.
</grounding_rules>
