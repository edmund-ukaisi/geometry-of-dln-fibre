<task>
Assess FORMALISATION BUILDABILITY in Lean 4 + Mathlib of a specific analytic brick, and whether an
alternative reduction avoids it. Judge independently; I withhold my leaning. Distinguish "reduces to
banked/standard pieces" from "needs machinery Mathlib lacks (resolution of singularities)."
</task>

<context>
A formaliser has ALREADY built (sorry-free) the "atom" that integrates out the corank block Γ for a
FIXED full-row-rank Q_b: the Gram change-of-variables det(Γ↦Γ·M)=(det M)^p, the linear-cov ∫⁻ formula,
the full-space isotropic radial endpoint, and posdef-sqrt via CFC (Analysis/Matrix/Order). So step-2
(fixed non-degenerate Q_b) is buildable. THE OPEN BRICK is the OUTER integral over the tail parameters,
where Q_b DEGENERATES (rank-drops) and Q_b is a matrix PRODUCT.
</context>

<the_brick>
Prove finiteness of an outer integral over box-bounded matrix parameters of
    det(Q_b Q_bᵀ)^{-(M0-t)/2} · core^{-(c'-a/2)},   a=(M0-t)(M1-t),  c' < ½·minAdm,
where Q_b (a (M1-t)×n block) is the NON-pivot rows of a matrix PRODUCT Q = A1·A2···A_{L-1}, so the
Gram determinant det(Q_b Q_bᵀ) degenerates on a locus SHARED with the "core" (reduced-chain loss)
through the deeper factors Z=A2···A_{L-1}. det(Q_b Q_bᵀ)^{-(M0-t)/2} → ∞ on {rank Q_b < M1-t}. The
designed proof monomialises det(Q_b Q_bᵀ)=‖∧^{M1-t}Q_b‖² into a normal-crossing ∏ b_i², tracking WHICH
exceptional coords are shared across generators (at corank ≥ 2 the sharing changes the value:
⟨δx,δy⟩ has RLCT ½, ⟨δ1x,δ2y⟩ has RLCT 1 — same widths, different value).
</the_brick>

<mathlib_inventory_facts>
EXISTS: PosSemidef of A Aᴴ; CFC matrix sqrt (det_sqrt/inv_sqrt/sq_sqrt, Analysis/Matrix/Order); Hermitian
spectral theorem / eigendecomposition; LDL S=LDLᴴ ONLY for positive-DEFINITE (nonsingular) S; Gram–Schmidt;
singular VALUES sequence (no matrix SVD factorisation); (A Aᵀ).rank=A.rank; exteriorPower Basic/Basis/Pairing;
det basics; general linear Haar change-of-variables (map_linearMap_addHaar_eq_smul_addHaar); a radial
blow-up residual-power lemma ∫(frobSq Γ + w)^{-c'} ≤ C·w^{-(c'-pq/2)} for c'>pq/2; a monomial box endpoint
∫∏|u|^{α}·unit < ∞ iff α_i>-1; Aoyagi Case-1/Case-2 single-radial blow-up charts formalised for a specific
(2,2,2) instance.
ABSENT: Cauchy–Binet (det(AB)=Σ minors, hence det(A Aᵀ)=Σ minors²=‖∧^q A‖²); ANY resolution of singularities
/ principalisation / blow-up / monomialisation / Newton polytope / log-canonical-threshold / determinantal-
variety machinery; a matrix decomposition valid ON the rank-drop (degenerate) locus.
</mathlib_inventory_facts>

<two_candidate_reductions>
R-ATOM (current architecture): integrate the corank block Γ OUT against Q_b in one shot, producing the
det(Q_b Q_bᵀ)^{-p/2} residual above; then the OUTER integral must principalise that Gram determinant of a
PRODUCT as Q_b degenerates.
R-BLOWUP (Aoyagi's native): do NOT integrate the block out; blow up ONE radial coordinate u for the whole
corank block (d-block = u·d', top-left normalised), integrate the single radial coordinate (charge = full
block codim), REDUCE the block by one pivot and RECURSE carrying the reduced block × the downstream product.
The fully-resolved loss becomes a monomial Σ b_i² (b_i = products of the u's), closed by the monomial
endpoint. No Gram determinant is ever formed.
</two_candidate_reductions>

<the_questions>
Q1. Is the R-ATOM outer brick — principalising det(Q_b Q_bᵀ)=‖∧^q Q_b‖² of a matrix PRODUCT into a
   normal-crossing monomial while tracking shared support at corank ≥ 2 — BUILDABLE by breaking into
   standard/banked pieces (name them), or does it genuinely require general resolution-of-singularities /
   determinantal-variety resolution Mathlib lacks? Rate A (break-it-down-buildable) / B (from-scratch RoS).
   Probe HARDEST at corank ≥ 2 shared-support — is that where a concrete chart cov fails?
Q2. Does R-BLOWUP AVOID the Gram-determinant principalisation entirely (Q1's hard object never forms)? If
   so, is R-BLOWUP itself break-it-down-buildable from the banked radial + monomial + Case-1/2 templates +
   general-L (S,J) chart algebra — or does the general-L step hide the same corank-≥2 obstruction? Be
   concrete about how corank ≥ 2 is handled by the single-radial-per-pivot chart.
Q3. Net: which route is the bounded formaliser runway, and the single hardest sub-brick of THAT route?
</the_questions>

<grounding_rules>
- Judge against the stated inventory; flag if you assert a lemma exists you are unsure of.
- Distinguish "elementary bounded lemma Mathlib lacks but is standard" (e.g. Cauchy–Binet) from "research-
  level singularity theory Mathlib lacks" (e.g. RLCT of determinantal varieties).
- Do NOT assume my preferred answer; I withhold it.
</grounding_rules>

<output_contract>
1. Q1 verdict (A/B) + decisive reason, focused on the corank-≥2 shared-support step.
2. Q2: does R-BLOWUP avoid it, and is R-BLOWUP buildable (concrete corank-≥2 mechanism)?
3. Q3: recommended route + its single hardest sub-brick.
</output_contract>
