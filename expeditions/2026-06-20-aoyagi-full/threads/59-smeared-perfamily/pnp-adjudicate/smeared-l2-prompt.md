<task>
I am adjudicating two analytic facts in a Lean/algebra formalization of the geometry of fibers of
deep linear networks. I want a DECORRELATED, exact-algebra second opinion. Do NOT rubber-stamp;
construct your own argument or counterexample.

SETUP (an L=2 deep linear network "smeared/boundary" stratum chart).
- Widths M0, M1, M2 are positive integers (the layer dimensions; L=2 means 3 layers indexed 0,1,2).
- A free matrix A0 is M0 x M1 (the "front" / layer-0 weight).
- A split r + s = M1 with r >= 1, s >= 0. Columns of A0 are split into the first r columns
  P1 := A0[:, 0:r]  (shape M0 x r)  and the last s columns  P2 := A0[:, r:M1] (shape M0 x s).
- Lam0 := (P1^T P1)^{-1} P1^T P2   (the normal-equations / least-squares routing, r x s).
- The chart needs the identity  P1 * Lam0 == P2   to hold (call it "the cancellation"),
  evaluated off the pole { det(P1^T P1) = 0 }.

In this stratum a "front-bottleneck" structural fact is claimed: the front product (here just A0,
since L=2) has generic rank exactly r, where r = min over front widths. The deepest analysis quantity
is the "deepRank" r, and the stratum is characterized by deepRank < deepRows.

QUESTION 1 (the cancellation). For the chart's FREE A0 (a generic M0 x M1 matrix), and a split
r + s = M1 with s > 0:
  (a) Under what exact condition on (M0, M1, r) does P1 * Lam0 == P2 hold for a GENERIC free A0
      off the pole? (Characterize precisely: when is col(P2) subset col(P1) automatic?)
  (b) For an L=2 smeared stratum where r is forced to equal min(M0, M1) (the front-bottleneck),
      what are the possible shapes of P1 (square / tall / wide), and does the cancellation then hold
      for a generic free A0? Enumerate the sub-cases (M0 < M1, M0 = M1, M0 > M1) and the value of
      s = M1 - r in each.
  (c) Is there any L=2 smeared configuration (with s > 0) in which P1 is genuinely TALL (r < M0)
      AND A0 is free/generic? If yes, give it; if no, explain why the bottleneck r = min(M0,M1)
      forbids it.

QUESTION 2 (the conditioned inverse-norm bound, "field A"). We need a bound of the form: on a
"conditioned" source box where the r x r block of P1 has its diagonal pinned in [delta/2, delta] and
all off-diagonal / residual coords are in [-delta/8, delta/8], every entry of Lam0 = (P1^T P1)^{-1}
P1^T P2 is bounded (e.g. |Lam0_ab| <= const independent of delta), so that every entry of the decoded
deep matrix A^1 = z*Hbar - Lam0 * S_bot stays <= 2*delta (giving containment of the conditioned box in
a target cube of radius ~2*delta). The (2,3,1) anchor proves this with an explicit 2x2 cofactor bound.
  (a) For general r (P1 the r x r conditioned block in the SQUARE case r = M0), what is the cleanest
      general estimate for ||(P1^T P1)^{-1} P1^T P2|| given the conditioning? State the key inequalities
      (Gram lower bound via Gershgorin / diagonal dominance, operator-norm of P1^T P2).
  (b) Does the bound survive r -> general (not just r=2), and what is the delta-scaling? Does the
      "diagonal pinned in [delta/2, delta], off-diagonals <= delta/8" conditioning give a Gram that is
      diagonally dominant / invertible with a quantitative lower bound on its smallest eigenvalue,
      uniformly in the entries? Give the explicit constant or its structure.
</task>

<output_contract>
- Answer Q1(a),(b),(c) and Q2(a),(b) separately and explicitly.
- For Q1: give the exact algebraic condition + the L=2 sub-case enumeration. If you claim the
  cancellation holds/fails in a case, give a concrete small exact-rational example or a one-line
  linear-algebra reason (rank/column-space).
- For Q2: give the proof STRUCTURE (named inequalities) and the explicit constant or its delta-scaling,
  plus any condition on r or on delta needed.
- Clearly separate FACTS (provable now) from INFERENCES/conjectures.
</output_contract>

<grounding_rules>
- Exact linear algebra only; no floating point as a proof.
- "col(P2) subset col(P1)" is the factoring P2 = P1*K; the cancellation reduces to that + Gram invertible.
- Be adversarial: actively look for the case where the cancellation FAILS for a free generic A0.
</grounding_rules>
