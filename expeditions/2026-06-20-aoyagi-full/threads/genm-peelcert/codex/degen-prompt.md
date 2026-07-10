<task>
Follow-up real-analysis question on the SAME Aoyagi-DLN RLCT change-of-variables as before (freed Schur
loss, chain of matrix widths). Now specifically about the DEGENERATE corner of one peel.

RECAP. Chart with pivot cut t, a=M₀−t, b=M₁−t, q=M_last. Corank tail block Q_b (b×q). The freed loss is
  freed = ‖B₀‖²_F + ‖C′·B₀ + Γ·Q_b‖²_F,   B₀ = reduced-chain product (t×q), Γ free (a×b).
On the FULL-ROW-RANK locus {rank Q_b = b} I have an EXACT clean factoring: cover {rank Q_b=b} by
dominant-b-minor charts (Cauchy-Binet det(Q_bQ_bᵀ)=Σ_{|S|=b} det(Q_b[:,S])²), and on each chart the
whole-ℝ^{ab} Γ-Morse peel gives det(Q_bQ_bᵀ)^{−a/2}·‖B₀‖^{ab−2c′}, the Gram is a smooth positive unit
(dominant minor bounded below by a fixed constant), and the integral is (radial monomial)×(reduced-chain
box integral at c′′=c′−ab/2). This closes for c′ < ½·minAdm(M) via the reduced-chain IH.

THE PROBLEM (the degenerate corner {rank Q_b < b}, e.g. near det Q_b=0 for square b=q):
I have checked, exactly, that near {rank Q_b < b}:
  (i) integrating Γ over ALL of ℝ^{ab} then estimating gives det(Q_bQ_bᵀ)^{−a/2} whose Q_b-integral
      DIVERGES when a ≥ q−b+1 (near a rank-(b−1) point det(Q_bQ_bᵀ)∼|z|², z∈ℝ^{q−b+1}, so
      ∼r^{q−b−a}dr; divergent for a≥q−b+1);
  (ii) a dyadic-shell sum in |det Q_b| of that lossy bound also diverges (Σ 2^{n(a−1)}, a≥1);
  (iii) bounding freed^{−c′} ≤ ‖B₀‖^{−2c′} (drop the corank term) and integrating over the tail box
        converges only for c′<1 (B₀ is a low-rank linear image of the tail), NOT up to ½·minAdm(M).
YET a direct Monte-Carlo of the full chart integral for M=(2,3,2), t=1 (a=1,b=q=2, ½·minAdm=2) is
finite for c′<2 and diverges only as c′→2. So the true integral over the degenerate corner IS finite up
to ½·minAdm(M); the three bounds above are all LOSSY there.

QUESTIONS (genuinely open — do not assume any particular resolution):
(Q1) What is the correct finite bound for the degenerate corner {rank Q_b < b} that reaches c′<½·minAdm(M)?
     In particular: is the right move (a) to KEEP Γ in its bounded box (not ℝ^{ab}) so the collapsing
     corank direction stays O(1) — a "box keeps the flat direction bounded" mechanism — and integrate the
     transverse directions with a codimension/Morse count; or (b) to recurse (the rank-(b−1) corner is a
     LOWER pivot cut / a deeper layer, closed by the reduced-chain recursion at its own minAdm); or (c)
     something else? Give the mechanism and the exponent count that reaches ½·minAdm(M).
(Q2) The codimension of {rank Q_b ≤ b−1} in the corank-tail space — call it D_deep. Is the correct
     statement an inequality "minAdm(M) ≤ D_deep + (charge)" analogous to a rank-flag linchpin, so the
     corner exponent stays below D_deep? If so what are D_deep and the charge for a 3-width chain
     (Q_b = the corank rows of A₁, b×M₂)?
(Q3) Is the degenerate corner genuinely part of the SAME peel (must be closed here), or is it covered by a
     DIFFERENT chart of the cover (a different dominant A₀-minor / different pivot cut t′) so that each
     single peel only ever needs its own full-rank locus {rank Q_b=b}? Which is it, and why?
</task>

<output_contract>
Answer Q1,Q2,Q3 in order. Give the mechanism + exponent count for Q1 concretely. Separate what you can
argue exactly from heuristics. Under ~500 words. Do not pad or hedge.
</output_contract>

<grounding_rules>
Real Frobenius. "minAdm" is the DLN zero-product codimension recursion minAdm(M)=min_t[(M₀−t)(M₁−t)+
minAdm(t,M₂,…)]; treat as a black-box integer with that recursion. Box = product of [−1,1] intervals.
Pen-and-paper math, not formalization.
</grounding_rules>
