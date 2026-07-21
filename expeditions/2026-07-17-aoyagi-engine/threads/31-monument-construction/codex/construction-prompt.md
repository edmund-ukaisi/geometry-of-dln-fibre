<task>
Independent design review of a resolution-of-singularities construction (Aoyagi 2013, deep linear
networks / RLCT). I am certifying that Aoyagi's Cases-1&2 recursive blow-up, at FULL generality (all
depths L, all width vectors), produces an object satisfying a fixed target record. Adjudicate the
soundness of the construction on three load-bearing points, and try to break each with an exact
counterexample or a named gap. Do NOT rubber-stamp; find the failure mode if there is one.

SETUP (facts, verified):
- The core is F = the family of entries of the matrix product ∏_{s=1}^{L} C^{(s)}, each C^{(s)} an
  M^{(s)}×M^{(s+1)} matrix of coordinates, at the origin (all C^{(s)}=0). We resolve the sum of squares
  ∑ F_ij² (= ‖∏C‖²_Frobenius). This is a genuinely singular point.
- Aoyagi's recursion maintains, indexed by (S,J), the ideal identity
  ⟨∏C⟩ = ⟨ diag(b_1,…,b_{M(S)}) · [[E_J,0],[0,D_J]] · ∏_{s>S} C^{(s)} ⟩,
  where M(S)=min{M^{(s)}: s≤S} (RUNNING minimum of reduced widths), D_J the residual block, and the b_i
  are monomials in the exceptional coordinates u_{s,k} introduced so far, with
  b_0=1, b_i = (∏_{ t̃_{s,k}=i-1 } u_{s,k}) · b_{i-1}.
  Here t̃_{s,k} ∈ {0,1,…} is a "threshold" the recursion assigns each divisor.
- Each step (Case 1 partial-block, or Case 2 full-block) blows up a determinantal locus; the chart
  introduces a new exceptional coordinate at threshold = current J (or augments an existing divisor's
  Jacobian exponent), then advances J (clears one unit pivot) or increments S. Terminates at S=L+1 with
  ⟨∏C⟩ = ⟨diag(b_1,…,b_{M(L+1)})⟩ and ‖∏C‖² = ∑ b_i² (normal crossing) in each terminal chart.
- Each exceptional divisor u_{s,k} carries Jacobian exponent M_{s,k}-1 (|det Dg| ∋ u_{s,k}^{M_{s,k}-1}).
- The terminal divisors (those with t̃_{s,k}=0) have accumulated exponent
  M_{s,k} = (M^{(1)}-t¹)(M^{(2)}-t¹) + Σ_{j=2}^{L}(t^{j-1}-t^j)(M^{(j+1)}-t^j),
  where t=(t¹,…,t^L) is the branch's weakly-decreasing rank profile; and
  rlct_core = ½ min{ M_{s,k} : t̃_{s,k}=0 }.
- The regular block-elimination transforms Q,P are UNIPOTENT/regular (unit Jacobian at the basepoint);
  Aoyagi uses them via "RLCT depends only on the ideal" (ideal-invariance), i.e. they are ideal-preserving
  generator changes, entries = polynomial/rational cofactors regular where a pivot minor ≠ 0.

THE THREE POINTS TO ADJUDICATE:

(1) DIVISIBILITY CHAIN AT FULL GENERALITY. Claim: from b_i = (∏_{t̃=i-1} u)·b_{i-1} one gets the closed
    form b_i = ∏_{ s,k : t̃_{s,k} < i } u_{s,k}, hence b_1 | b_2 | … | b_M (nested index sets), and each
    new coordinate introduced at threshold J multiplies exactly the SUFFIX b_{J+1},…,b_M — preserving
    b_i | b_{i+1} through every step type. Is this closed form + chain-preservation forced by the update
    rule, at all L / all width vectors? Is there a step type or a non-monotone-width configuration where a
    newly introduced coordinate would multiply a NON-suffix (some b_i with i≤J), breaking the chain? Also:
    is b_1 = ∏_{t̃=0} u ALWAYS a nontrivial monomial (≥1 terminal divisor), and is it SQUAREFREE (each
    coordinate to power ≤1)?

(2) UNIT NONVANISHING vs COVER (the far-region tension). The composed chart map g = (monomial blow-up
    substitutions) ∘ (regular transforms). |det Dg| = (monomial ∏u^{M_{s,k}-1}) × (unit), unit = product
    of regular-transform pivot-determinants, nonvanishing at the chart origin. For the target record the
    unit AND the ideal-identity cofactors must be continuous+nonvanishing on an OPEN set `nbhd`, and a
    COMPACT `dom ⊆ nbhd` whose g-images (finitely many charts) a.e.-cover a neighborhood of 0. Concern:
    to cover a ball, the standard blow-up affine charts need domains LARGE in the projective directions
    (y_j = x_j/x_i ∈ [-1,1]), but the pivot minors are only guaranteed ≠0 NEAR the origin — could a pivot
    minor vanish on the covering (anisotropic) domain, so no single nbhd both carries the certificates and
    contains a covering dom? Is this a genuine obstruction, or does the projective-chart structure (chart
    i = locus where the i-th minor is the invertible pivot) keep the relevant pivot a unit on the whole
    chart domain? Where exactly does the compact-domain / a.e.-cover bookkeeping become nontrivial?

(3) MIN-ATTAINMENT / NO-UNDERSHOOT. The record's lower-bound obligation quantifies over the binding axes
    of the dominant monomial b_1, i.e. over {u_{s,k} : t̃=0} = the terminal divisors, requiring for each
    such axis: qipMin ≤ (Jacobian exponent + 1) = M_{s,k}, plus SOME axis attains qipMin. Here qipMin =
    min over feasible e (∑e_i = M^{(1)}, the antidiagonal) of G(e) = Σ_{j≤i} e_i(e_j + d_j - d_{j-1}),
    which equals min over admissible rank-profiles of the codimension M_val(t). Question: is every terminal
    divisor's accumulated exponent M_{s,k} equal to M_val(t) for an ADMISSIBLE (feasible) profile t — so
    that M_{s,k} ≥ qipMin automatically — even at NON-MONOTONE width vectors (e.g. (2,2,3,2))? There is a
    known transcription defect (a divisor "labelled" with a raw-width profile (2,3,0) that is NOT
    weakly-decreasing/admissible, yet whose PHYSICAL accumulated exponent is M_val(2,2,0)=4, an admissible
    value). Does reading the physical accumulated exponent (running-min governed) — rather than any
    raw-width label — guarantee every terminal exponent is an admissible M_val, hence ≥ qipMin? Are there
    terminal divisors whose physical exponent could be < qipMin (undershoot)?
</task>

<output_contract>
Three sections, (1)/(2)/(3), matching the points above. For each: VERDICT (sound / unsound / gap-named),
then the reasoning, then either the exact counterexample that breaks it OR the precise reason it holds
and the named residual bookkeeping if any. Be concrete about L and width vectors. If a point is a genuine
frontier (detail-at-scale vs new-math), say which. End with the single most likely thing to be wrong.
</output_contract>

<grounding_rules>
- Exact algebra only for anything load-bearing; a plausibility argument must be labelled as such.
- This is resolution of singularities of a determinantal / matrix-product ideal; reason from the
  ideal/blow-up structure, not from analogy.
- Do not assume the construction is correct because "the paper does it" — the paper has a known
  transcription defect (point 3). Find where a general-L / non-monotone-width configuration breaks a claim.
- Distinguish clearly what you can PROVE from what you conjecture.
</grounding_rules>
