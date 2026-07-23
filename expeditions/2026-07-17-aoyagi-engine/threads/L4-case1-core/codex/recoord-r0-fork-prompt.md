<task>
Setting: Lean/Mathlib formalisation of Aoyagi's resolution of deep-linear-network singularities. A
resolution fold: `foldResid p` is the residual after a sequence of block blow-ups + unipotent shears.
The step shear (baked def `canonNormalizationOf`) writes two supports: (i) a pivot-shifted Schur
cross-term on layer S's interior, (ii) a "deeper recoord" `A_{S+1} → A_{S+1}·Q₁⁻¹` on layer S+1.
The shear MUST be UNIPOTENT (Jacobian det = 1) — this is a load-bearing field the RLCT computation rides.

CONFIRMED DEFECT (verified, exact sympy): the baked shear omits the pivot-COLUMN clear (the `Q₁·A_S`
half of Aoyagi's `A_{S+1}·A_S = (A_{S+1}·Q₁⁻¹)·(Q₁·A_S)`). On the smallest boost witness d=(2,2,2,2),
at the case-11 boost parent, the residual slot 0 is:
    foldResid[0] = u₁₀₀ + 2·u₀₁₀·u₁₀₁      (baked)
  vs canonShearOf (Schur only, no recoord): u₁₀₀ + 1·u₀₁₀·u₁₀₁
  vs FULL clear (Schur + recoord + column clear): = w₁₀₀  (running frame w₁₀₀ = u₁₀₀ + u₀₁₀·u₁₀₁, clean).
The unpaired recoord DOUBLES the defect (1 → 2). Reading foldResid[0] as a degree-1 form in the layer-1
column coords: partial-block coeff c_{u₁₀₀} = 1, extra-block coeff c_{u₁₀₁} = 2·u₀₁₀.

DIVISOR STRUCTURE at the case-11 node (branch: ed1 case2 births div0 at corner (0,0), t̃=0, exceptional
= u₀₀₀; ed2 case2 births div1 at corner (0,1), t̃=1, exceptional = e₂ = u₀₁₁ − u₀₁₀·u₀₀₁ [the Schur value
in the running frame]; ed3 rollover to layer 1; the case-11 REUSES div1, so the boost pivot = div1's
exceptional = e₂). Aoyagi's carried invariant (worked.tex:562-577): `⟨∏C⟩ = ⟨diag(b_1..b_{M(S)})·[E_J|D_J]·∏C^{(s>S)}⟩`
with b_0=1, b_i = ∏_{t̃<i} (exceptionals) — the b-monomials multiply the residual's ROWS; D_J's entries
are otherwise arbitrary.

THE RULED FIELD (the invariant the formalisation carries): for each active divisor k, the extra-block
coefficients (col ≥ t̃_k) factor as c_i = m_k·β_i, m_k = the divisor's exceptional (running-frame
COMBINATION, e.g. e₂), β_i continuous.
</task>

<output_contract>
Answer in ≤700 words, R0 FIRST (it may short-circuit the rest):

R0 — DOES the baked def already SATISFY the ruled field (making the crisis a false alarm — the
`honest_clear`-matching bar would then be testing the full-clear MODEL, not Aoyagi's invariant)?
Concretely: is the extra-block coefficient `c_{u₁₀₁} = 2·u₀₁₀` expressible as `m_k·β` where m_k is an
active divisor's exceptional (u₀₀₀, or e₂ = u₀₁₁−u₀₁₀·u₀₀₁) and β continuous? Is bare `u₀₁₀` any active
divisor's exceptional / b-factor (raw or Schur combination)? If the reused divisor's exceptional is e₂,
can `2·u₀₁₀ = e₂·β` for continuous β? Rule R0 YES or NO with the reason. Separately: the coeff 2 — under
R0-YES it must trace to a real b-step (not an error); does it? VERDICT: R0-YES (field lands on current
def, model fork moot) or R0-NO (crisis real, fork proceeds).

THEN, only if R0-NO, the fork (rank each; cheapest discriminating test for each):
R1 — drop the recoord (branch ii), revert to canonShearOf (coeff 1), and source boost-readiness
differently. Does canonShearOf's residual (extra carries u₀₁₀, coeff 1) match the ruled field for SOME
divisor assignment, or is u₀₁₀ genuinely not a b-factor there either?
R2 — the δ=1 blow-up handling is incomplete: the strict transform (currently pivot→1, else→value) should
reparametrize the whole center so the column clear happens via the CHART (not a unipotent shear),
realizing Aoyagi's clear at the correct Jacobian. Is this the standard resolution picture?
R3 — a unipotent realization of the paired clear that I have not seen.
Flag which claims are logical necessity vs plausible-unverified.
</output_contract>

<grounding_rules>
Design-feasibility, not Lean code. The clearing coefficient in Aoyagi's Q₁ is γ = A_S[row][b]/A_S[a][b]
(a DIVISION by the pivot); the fold order is shear-on-u THEN quotient (pivot→1), so at shear time the
pivot is still the exceptional coordinate (not 1). Do not assume the pivot is normalized at shear time.
Distinguish "follows from Aoyagi's invariant as stated" from "true in the full-clear model." If R0
hinges on a fact about her b-monomial row-assignment I have not pinned, name it as the assumption.
</grounding_rules>
