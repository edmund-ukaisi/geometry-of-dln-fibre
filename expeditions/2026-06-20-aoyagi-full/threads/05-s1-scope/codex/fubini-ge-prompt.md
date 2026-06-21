<task>
Decorrelated fidelity check of a Lean RLCT lemma (the ≥-direction of a "smooth-block Fubini" RLCT lemma).
Judge whether the integrability lemma establishes the CORRECT condition for the intended ≥-bound, and
whether a hygiene hypothesis is faithful.

CONTEXT: RLCT λ(F) at a point = sSup{ c ≥ 0 : |F|^{-c}·(weight) is locally integrable near the point }.
GOAL lemma (eventual): `rlctAt(‖x‖² + G(y)) = n/2 + λ_core(G)` where x ∈ ℝⁿ (a regular quadratic block),
G(y) the singular core. This audit covers only the ≥ (lower-bound) direction.

THE LEMMA UNDER AUDIT (`joint_integrableOn_weighted`):
Hypotheses: n = m+1; a,b > 0; G ≥ 0 measurable; w ≥ 0 measurable (a Jacobian weight);
  `hGne : G ≠ 0 a.e. on V`;
  `hx : ‖x‖^{-2a} integrable on ball(0,ε) in ℝ^{m+1}` (which holds iff 2a < m+1, i.e. a < n/2);
  `hy : |G|^{-b}·w integrable on V`.
Conclusion: `|‖x‖² + G(y)|^{-(a+b)}·w(y) integrable on ball(0,ε) ×ˢ V`.
Proof: pointwise a.e. comparison `(s+t)^{-(a+b)} ≤ s^{-a}·t^{-b}` (s=‖x‖²>0 a.e., t=G>0 a.e. by hGne),
then `Integrable.mul_prod` of the two halves dominates the joint.

QUESTIONS:
1. Does this lemma establish the RIGHT condition for the ≥-direction `rlctAt(‖x‖²+G) ≥ n/2 + λ_core`? I.e.:
   given a<n/2 and b<λ_core, the joint exponent c=a+b is admissible; and splitting c=a+b with a<n/2,b<λ_core
   covers every c < n/2+λ_core, so the admissible set ⊇ [0, n/2+λ_core), giving rlctAt ≥ n/2+λ_core. Confirm
   the logic and that the comparison `(s+t)^{-(a+b)} ≤ s^{-a}t^{-b}` is in the correct (domination) sense.
2. Is the comparison bound `(s+t)^{-(a+b)} ≤ s^{-a}·t^{-b}` (s,t>0, a,b≥0) actually TRUE? Any edge case
   (a=0 or b=0; the lemma uses a,b>0)? Is dominating the joint ABOVE by an integrable function the right
   move to conclude the joint integrable?
3. Is `hGne : G ≠ 0 a.e. on V` the right hygiene hypothesis, faithful to a use-site where G is a resolved
   monomial core `∏_j |y_j|^{2k_j}` (vanishing only on null coordinate hyperplanes)? Does it correctly dodge
   the known failure mode (G germ-vanishing on a positive-measure set ⟹ rlctAt(G)=⊤ ⟹ the bound is false)
   WITHOUT assuming away a case the monomial use-site actually hits?
</task>

<output_contract>
Three numbered verdicts, terse: CONFIRMED/FLAG + one-or-two-line reason. For Q2 confirm the inequality and
note any a=0/b=0 edge. For Q3, faithful/unfaithful + whether the monomial core satisfies hGne.
</output_contract>

<grounding_rules>
Separate rigorous fact from inference (flag inferences). The rpow base-monotonicity and the
dominated-convergence/Integrable.mono direction are standard; use them. Don't invent Mathlib lemma names.
</grounding_rules>
