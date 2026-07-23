<task>
Decorrelated council read on a formalisation-fidelity fork. We formalise Aoyagi's DLN
resolution-of-singularities recursion in Lean. A def-level defect (a recoord with the wrong
inverse direction) was just found; fixing it may reveal that an EARLIER ruling (a "carried field")
was fitted to the broken def's symptom rather than to the paper. Judge Aoyagi's MATH; do NOT trust
our Lean encoding. Flag INFERENCE vs FACT.

=== AOYAGI'S TEXT (verbatim, worked reproduction) ===
Theorem 3 step S→S+1: given Q'_1(∏_{s≤S}A^(s))Q'_2 = [[C'_1,0],[0,∏_{s≤S}C^(s)]], put
  A'^(S+1) = Q_2'^{-1} A^(S+1)   ...(worked.tex:445)
then clear bottom-left with Q''_1 and top-right with Q''_2, giving the next Schur complement C^(S+1).

The inductive invariant maintained by the blow-up recursion, indexed by (S,J):
  ⟨∏_{s=1}^L C^(s)⟩ = ⟨ diag(b_1,…,b_{M(S)}) · [[E_J, 0],[0, D_J]] · ∏_{s=S+1}^L C^(s) ⟩   ...(worked.tex:565-567)
where D_J is the (M(S)−J)×(M^(S+1)−J) residual block, b_i monomials in the exceptional coords u_{s,k}
(b_0=1, b_i=(∏_{t̃=i−1}u_{s,k})b_{i−1}), so b_1|…|b_M by construction.

The blow-up step, Case 1 (partial equal run of the b-sequence above J):
  Case 1(1): "the d-block = u_{s,k}·d'" sets t̃_{s,k}=J and adds M'_{s,k}=M_{s,k}+J_1(M^(S+1)−J).   ...(worked.tex:615)
  Case 1(2): first row normalised, u_{s,k}=u_{S,J+1}u'_{s,k}, introduces u_{S,J+1}; regular Q,P reduce
             D_J'' → [[1,0],[0,D_{J+1}]].

=== THE TWO QUESTIONS ===

Q1 (RECOORD DIRECTION). In the Lean product order (mult = A_{N-1}···A_1·A_0, the REVERSE of Aoyagi's
∏_{s=1}^L), the deeper-factor recoord that compensates for clearing layer S's pivot column: is it
A_{S+1}·Q₁ or A_{S+1}·Q₁⁻¹ (where Q₁ = [[1,0],[γ,1]] is the unipotent that clears the pivot column,
γ the below-pivot ratio)? A prior certificate wrote A_{S+1}·Q₁⁻¹ (+γ); an explicit check finds +γ
DOUBLES the uncleared contribution (coeff 2) while −γ (= A_{S+1}·Q₁) CANCELS it (coeff 0), both
unipotent. Reason from worked.tex:445 (A'^(S+1)=Q_2'^{-1}A^(S+1), a LEFT-mult by an inverse in HER
order) transposed/reversed into the Lean order: which direction makes the product invariant and
cancels the base's uncleared cross-term? State the sign and the reason.

Q2 (THE INVARIANT SHAPE — the load-bearing one). At a Case-1(1) REUSE node, does Aoyagi's carried
residual (the object her invariant maintains between steps) have its EXTRA columns (the part of D_J
beyond the boost center) CARRY the exceptional coordinate as a factor, or are they CLEAN (the
exceptionals living OUTSIDE the block, in the diag(b) factor / the exponent ledger)?
- Reading A ("extras carry the exceptional"): the residual block's extra columns have coefficients
  divisible by the reused divisor's exceptional; the b-chain lives INSIDE the block.
- Reading B ("extras clean"): worked.tex:565-567 writes diag(b)·[[E_J|D_J]] with the b's OUTSIDE the
  block, so D_J itself is clean; the b-chain lives in the diag/ledger, and Case-1(1)'s "d-block =
  u_{s,k}·d'" is a TRANSIENT factoring DURING the blow-up, not a property of the carried invariant.
Which reading is faithful to her INVARIANT (the object carried between steps), as opposed to the
transient blow-up step? Note the subtlety: the ACTUAL product matrix diag(b)·[block] has b-SCALED
rows (extras would carry b's), but the CARRIED normal form separates diag(b) from a clean block.
If Reading B, then a "boost-readiness" property (residual degree-1 supported on the smaller center
{pivot}∪partial-block) follows DIRECTLY from a clean block (extras vanish on the center), needing NO
separate "extra-block coefficients factor by the exceptional" hypothesis. If Reading A, that
hypothesis is a genuine carried invariant. Which is it, per her text?
</task>

<output_contract>
Two sections:
1. Q1 — the recoord direction (A_{S+1}·Q₁ or ·Q₁⁻¹), the sign, and the one-line reason from
   worked.tex:445 in the reversed product order. CONFIRMED/UNCERTAIN.
2. Q2 — Reading A vs Reading B, with the reason from worked.tex:565-567 (b's inside vs outside the
   block) and worked.tex:615 (is "d-block = u_{s,k}·d'" a carried-invariant property or a transient
   step). If Reading B, state explicitly that boost-readiness follows from the clean block with no
   extra-block-factoring hypothesis. Flag INFERENCE vs FACT; if her text is genuinely ambiguous on
   whether the CARRIED object is the clean block or the b-scaled product, say so.
</output_contract>

<grounding_rules>
Reason from Aoyagi's quoted text + standard resolution-of-singularities / monomialisation practice.
You may NOT assert our Lean encoding is right or wrong. Mark inference-from-standard-practice as
INFERENCE. If the text is ambiguous on the carried-object-vs-transient-step distinction, say so
rather than guess — that ambiguity is itself the answer we need.
</grounding_rules>
