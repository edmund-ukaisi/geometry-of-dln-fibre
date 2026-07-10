<task>
Real-analysis / resolution-of-singularities question about a specific change-of-variables in
an Aoyagi-style RLCT (real log canonical threshold) computation for deep linear networks.

SETUP (all objects concrete). Fix integers M₀,M₁,…,M_L (a "chain" of matrix widths), a pivot
cut t with 0≤t≤min(M₀,M₁), and write a=M₀−t, b=M₁−t, q=M_L (the last width). A per-chart
"freed Schur loss" is the real-analytic function of blocks

  P  (t×t, invertible),  B₁₂ (t×b),  C (a×t),  Γ (a×b free),  and a tail matrix
  Q̃  ((t+b)×q), split as Q_p = top t rows, Q_b = bottom b rows,

defined by   Q̃ₚ := Q_p + P⁻¹ B₁₂ Q_b   (t×q)  and

  freedSchurLoss = ‖P·Q̃ₚ‖²_F  +  ‖C·Q̃ₚ + Γ·Q_b‖²_F     (Frobenius squared).

The tail Q̃ = (A₁·A₂···A_L) reindexed, where A₁ is M₁×M₂, …; so Q̃ depends multilinearly on
the tail matrices A₁,…,A_L, and Q_p,Q_b are its row blocks. The chart integral is

  ∫ over (A₁,…,A_L)∈[−1,1]^·, (P,B₁₂,C)∈[−1,1]^· with P a unit, Γ∈(translated unit box)
     freedSchurLoss^(−c′)   dLebesgue.

"peelCharge" := a·b. The "reduced chain" is redChain = (t, M₂, …, M_L): the first TWO widths
(M₀,M₁) collapsed to the single pivot rank t; its product is a t×q matrix. There is a known
exact combinatorial identity  minAdm(M) = min_t [ (M₀−t)(M₁−t) + minAdm(redChain_t) ], and at
the binding cut t*  minAdm(M) = peelCharge + minAdm(redChain). Threshold of interest:
c′ < minAdm(M)/2.

WHAT I TRIED (facts, exact where noted):
1. freedSchurLoss is degree-2 homogeneous in the tail Q̃: freed(u·Q̃)=u²·freed(Q̃). (exact)
2. Integrating Γ over ALL of ℝ^{ab} (upper bound) gives, exactly for c′>ab/2,
     ∫_{ℝ^{ab}} freed^{−c′} dΓ = K(a,b,c′)·det(Q_b Q_bᵀ)^{−a/2}·‖P·Q̃ₚ‖_F^{ab−2c′}
   with K a finite Beta/Gamma constant; here P·Q̃ₚ = P·Q_p + B₁₂·Q_b =: B₀ (t×q). (verified
   exactly for the (2,2,1),t=1 scalar case with sympy; residual 0.)
3. B₀ = [P | B₁₂]·Q̃ = (pivot rows of A₀)·A₁·A₂···A_L is a t×q matrix — the SAME shape as the
   product of the reduced chain redChain. Its Frobenius-square appears at exponent
   c′′ := c′ − peelCharge/2.
4. For the smallest case (2,2,1),t=1 (all blocks scalar): a Monte-Carlo of the full 6-dim chart
   integral shows it is finite for c′<1 and diverges as c′→1 (=minAdm/2).

THE QUESTIONS (this is a genuinely open adjudication — do not assume it works or fails):
(Q1) Can the chart integral be written EXACTLY (equality, no Hölder / no p>1 split) as
     (a one-dimensional monomial radial factor  ∫ u^{α} du  for some explicit α)
     ×  (the reduced-chain box integral ∫ ‖prod(redChain)·Bnew‖_F^{−c′′} dBnew, c′′=c′−peelCharge/2)?
     If yes: what is the exact change of variables and the exact Jacobian exponent α (in terms of
     M₀,M₁,M₂,q,a,b,t)? If not exactly, what is the precise obstruction and on what sub-region
     (chart) does an exact factorization hold?
(Q2) The factor det(Q_b Q_bᵀ)^{−a/2} from step 2 is singular where Q_b loses row rank. Does a
     resolution (radial blow-up of the tail / a coordinate chart where a b×b minor of Q_b is
     bounded below) turn det(Q_b Q_bᵀ)^{−a/2}·dLebesgue into a NON-negative-power monomial times a
     smooth measure — i.e. is the Gram singularity genuinely removable by the blow-up, or does it
     leave a residual singularity that must be handled some other way (e.g. by NOT integrating Γ
     over all of ℝ^{ab} where Q_b is degenerate)? Be concrete about the b>1 case.
(Q3) Is the radial factor's convergence threshold on c′ genuinely ABOVE minAdm(M)/2 (so the
     reduced-chain integral is the binding constraint), or can the radial bind first?
</task>

<output_contract>
Answer Q1, Q2, Q3 in that order. For Q1 give the exact CoV + Jacobian exponent α if it exists,
else the exact obstruction + the sub-region where it holds. Keep it under ~500 words. Separate
what you can prove exactly from what is heuristic. Do not pad.
</output_contract>

<grounding_rules>
Frobenius norm, real matrices. "minAdm" is the DLN zero-product-locus codimension recursion given
above; treat it as a black-box integer function with the stated binding-cut identity. The Γ
Gaussian-type integral in step 2 is standard; you may use it. Do not invent Mathlib lemmas — this
is a pen-and-paper math question, not a formalization question.
</grounding_rules>
