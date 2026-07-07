<task>
Adjudicate ONE question, independently. Two internal documents disagree; I present BOTH neutrally and
withhold which I favor. Keep me honest.
</task>

<setup>
Resolving F = ‖C¹·C²···C^L‖² at 0 to compute RLCT = ½·minAdm (minAdm the layer-peeling min-codim; the
VALUE is independently certified). Aoyagi's construction maintains an invariant
  ⟨∏C⟩ = ⟨ diag(b₁,…,b_{M(S)}) · [[E_J,O],[O,D_J]] · ∏_{s>S}C^{(s)} ⟩,
b_i monomials in exceptional coords u_{s,k} (b_i = ∏ u), and advances by:
  Case 2 (FULL equal run b_{J+1}=…=b_{M(S)}): blow up the WHOLE residual block with ONE radial u,
    charge = full block codim, reduce D_J → diag(1, D_{J+1}), advance J.
  Case 1 (PARTIAL equal run b_{J+1}=…=b_{J+J₁} ≠ next): blow up a PARTIAL sub-block; sub-case 1(1) is an
    INNER recursion that ADDS to an EXISTING divisor's exponent (blows up along a previously-introduced
    u), merging exponents for the SHARED block; 1(2) introduces a new u.
Terminal: ∏ diagonal ⟹ ‖∏C‖² = Σ b_i² (normal crossing); RLCT = ½ min terminal exponent = ½minAdm.
</setup>

<two_claims_to_adjudicate_between>
CLAIM-A (a de-risking probe): the resolution is "single-radial-per-block iterated" — one radial per block,
sequential, each step reducing corank-k to corank-(k−1)+Morse via Z-independent unit transforms; the
earlier radials factor out as passive monomial prefactors, so deeper resolution is independent. Verdict:
BOUNDED (iterated explicit charts + the banked monomial endpoint). Caveat it flagged: "must still prove
the layer-by-layer single-radial blow-ups actually reach normal crossing."
CLAIM-B (an outer-construction note + a carrier-builder's escalation): the coupled diag(b) resolution with
SHARED exceptional variables across corank-≥2 blocks is "genuinely-new resolution-of-singularities, NOT
labor" — the shared-support at arbitrary corank ≥ 2 needs a SIMULTANEOUS principalisation, not a per-block
iteration.
Data point (certified): a per-ROW / one-blow-up / threshold-only model UNDERCOUNTS at corank ≥ 2
(e.g. (3,3,4): correct 4 vs per-row 3); "which exceptional variables are SHARED" changes the value
(⟨δx,δy⟩ has RLCT ½ vs ⟨δ₁x,δ₂y⟩ has RLCT 1 — identical widths/multiplicity, different value); per-row
holds only corank ≤ 1. L=2 single-block ‖XY‖² is fully banked (the Schur recursion, all widths).
</two_claims_to_adjudicate_between>

<the_question>
Is the GENERAL corank-≥2 shared-exceptional recursion (arbitrary widths, ≥2 coupled blocks sharing
exceptional divisors):
  (a) BOUNDED — the SAME iterated single-radial blow-ups (Aoyagi Cases 1&2), sequential, with the shared
     support tracked by the diag(b)/SJState invariant (the equal-run bookkeeping, Case-1 merging into an
     EXISTING divisor); explicit charts, NOT abstract Hironaka; lands on the banked monomial endpoint; OR
  (b) A GENUINE WALL — the shared support at arbitrary corank ≥ 2 requires a SIMULTANEOUS principalisation
     that is NOT a sequence of explicit single-block blow-ups (an abstract resolution-of-singularities
     Mathlib lacks)?
Specifically: (i) Are CLAIM-A's "iterated single-radial-per-block" and CLAIM-B's "coupled diag(b)
shared-support" the SAME object, or does coupled diag(b) do MORE (the Case-1 equal-run merging that a
naive fresh-per-block iteration misses)? (ii) Is the Case-1 "blow up along an existing divisor / merge
exponents" step a bounded EXPLICIT blow-up (sequential), or does it require a simultaneous/non-sequential
move? (iii) Does the per-row UNDERCOUNT show that naive per-block FAILS (⟹ the shared tracking is
necessary), but is the shared tracking still bounded explicit-chart bookkeeping?
</the_question>

<grounding_rules>
- Distinguish PROVE / argue / heuristic. The VALUE ½minAdm is certified — the question is the STRUCTURE
  (bounded iterated-explicit vs unbounded simultaneous res-of-sing).
- Aoyagi's Cases 1&2 are hand-constructed explicit charts (not an invocation of general Hironaka). Weigh
  whether that makes the build "bounded explicit labor" even if intricate.
- Do NOT assume either claim; both are internal and I withhold my lean.
</grounding_rules>

<output_contract>
1. VERDICT: (a) bounded-iterated-explicit | (b) genuine-wall-simultaneous | genuinely-uncertain.
2. Are CLAIM-A and CLAIM-B the same object? Does coupled diag(b) do MORE than fresh-per-block?
3. Is the Case-1 shared-divisor merging a bounded explicit blow-up or a simultaneous move? — the crux.
4. If (a): what exactly is the necessary genuinely-new content (the carrier bookkeeping) — and why bounded.
   If (b): the precise configuration where explicit iterated blow-ups cannot reach normal crossing.
</output_contract>
