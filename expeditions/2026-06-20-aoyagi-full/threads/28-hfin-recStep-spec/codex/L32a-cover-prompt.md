<task>
You are a measure-theory / real-algebraic-geometry second opinion on a change-of-variables COVER design
in a formalisation (Lean 4 + Mathlib) of a real-log-canonical-threshold (RLCT) upper bound. I want your
INDEPENDENT analysis of whether a proposed atlas covers a singular locus up to measure zero, and whether
the per-chart change-of-variables is correct. Do NOT assume my design is right; attack it.
</task>

<grounding>
SETUP (exact). We must show finiteness of a Lebesgue integral
    ∫_{U} |F(x)|^{−c'} dx < ∞   for all c' < λ,
where U ⊂ ℝ^N is a bounded open box around 0, F ≥ 0 is a real-analytic loss, and λ is a known rational
threshold (= ½·minAdm, a codimension/2). The singular content at the deepest point reduces, after an
established frame transport, to a determinantal core

    G(Δ, S) = ‖Δ · S‖²_F   (squared Frobenius norm of the matrix product),

where Δ is an r×r real "residual" matrix block and S is an r×p real free block, near (Δ,S) = (0, free).
The smallest binding case is r=2, p=4 (this is the inner core of the dimension vector (3,3,4), whose
full achiever cell is ‖T‖² ⊕ G with T a clean 1×4 Morse spectator block, disjoint variables).

PROPOSED COVER (the thing to attack). To resolve the {Δ = 0} singularity, blow up Δ radially:
  - View Δ as r² flat coordinates d_{ij}.
  - Atlas = r² affine "entry charts", chart-(i,j) = { d | d_{ij} ≠ 0 and |d_{kl}| ≤ |d_{ij}| ∀(k,l) }
    (i.e. entry (i,j) is the max-modulus entry).
  - On chart-(i,j): set a := d_{ij} (the scale), R := the matrix with R_{ij}=1 and R_{kl}=d_{kl}/d_{ij}
    (so |R_{kl}| ≤ 1, a bounded "angular" matrix), and Δ = a·R. The chart map is
        φ_{(i,j)}(a, R-ratios, S) = (a·R, S),  i.e. the standard monomial pivot blow-up on the d-entries,
    identity on S.
  - Claim A (COVER UP TO NULL): the r² charts cover {Δ ≠ 0}; the complement {Δ = 0} (all r² entries zero)
    is a codim-r² null subspace.
  - Claim B (PER-CHART JACOBIAN): |det Dφ| = |a|^{r²−1}.
  - Claim C (INTEGRAND): G ∘ φ = a²·‖R·S‖².
  - Claim D (RANK STRATIFY): on chart-(i,j), rank R ≥ 1 always (pivot entry =1); stratify by rank R = j.
    On rank-j stratum, after a Schur normal form, ‖R·S‖² ≃ (bounded-below unit)·‖P‖² + ‖B·Q‖² with P a
    j×p full-rank Morse block and B·Q a corank-(r−j) lower determinantal core. RECURSE on the lower core
    (corank strictly drops, r−j < r). Leaves: Euclidean Morse blocks ‖·‖² (radially integrable) and the
    1-D monomial divisor a².
  - Claim E (THRESHOLD): the chart finiteness threshold = min(r²/2 [the a-divisor],
    min_{1≤j≤r}( jp/2 + λ_{r−j,p} ) [rank strata, Morse-block-dim/2 ADDED to lower-core λ]). Define
    λ_{r,p} by this recursion, λ_{0,p}=0. We computed λ_{2,4}=2, λ_{3,4}=4, λ_{3,3}=7/2, λ_{4,4}=6.
</grounding>

<facts_established>
- The monomial pivot blow-up map, its argmax-cell cover {d_p≠0, ∀k |d_k|≤|d_p|}, its a.e.-disjointness,
  its Jacobian det = (pivot)^(#active − 1), and its image characterisation are ALREADY proven in the
  Lean library at the r² entry level (a generic "argmaxCellOn / pivotBlowupOn" family on Fin (r²) → ℝ).
- Exact (sympy) checks I have run: Jacobian det = a^{r²−1} for r=2,3; G∘φ = a²·‖R·S‖² (a-degree exactly 2)
  for r=2,3; det R factor identifies the rank-drop locus; the rank-1 Schur split
  ‖R·S‖² = (1+v²)·‖[1,u]·S‖² on the rank-1 stratum (r=2); the λ recursion reproduces ½·minAdm on
  (2,4),(3,4),(3,3),(4,4),(2,2).
- A disjoint-variable Morse block ⊕ lower core has rlct = (Morse dim)/2 + (lower rlct) by Fubini/Tonelli.
- The terminal Morse leaf ∫_{box} (∑ Pᵢ²)^{−c'} < ∞ ⟺ c' < (dim P)/2 is proven (radial integration).
</facts_established>

<questions>
1. COVER. Is Claim A correct that the r² entry charts cover {Δ ≠ 0} up to a null set, with the chart
   domains as stated (non-pivot ratios bounded by 1)? Is there any subtlety in covering {Δ ≠ 0} (not just
   the all-entries-equal-modulus tie set) — e.g. does the bounded-ratio domain miss part of an argmax cell?
2. C-O-V VALIDITY. The change of variables ∫_{φ(domain)} g = ∫_{domain} |det Dφ|·g∘φ requires φ injective
   off {a=0} and C¹. Are there hidden non-injectivity or boundary issues when φ maps the bounded-ratio
   domain ONTO the argmax cell? Does the {a=0} exceptional locus being null suffice to drop it?
3. RANK STRATIFICATION as a COVER. Claim D stratifies the chart by rank R. For the MEASURE-THEORETIC cover
   to close, do I need the rank-(<r) strata {det of some minor = 0} to be handled as null sets PLUS a
   recursive resolution, or does the rank-drop locus genuinely need its own blow-up (it has positive
   codim but the integral can still diverge there)? Concretely at r=2,p=4: the rank-1 locus {det R = 0}
   is codim-1 in R-space — is it correct that I must RESOLVE it (not just drop it as null), because the
   integrand ‖R·S‖²^{−c'} can blow up faster than codim-1 there?
4. THRESHOLD COMBINATION. Is the per-chart threshold the MIN of (a-divisor r²/2) and (the rank-strata
   recursion), as in Claim E? Specifically: the a-axis is a separate radial factor (Tonelli product), so
   the chart is finite iff BOTH the a-integral and the inner (R,S)-integral are finite — hence MIN. But
   WITHIN the inner, the Morse-block ⊕ lower-core is a disjoint SUM, so rlct ADDS. Is this min-of-(divisor,
   sum-recursion) the right combination, or is there a coupling between a and (R,S) I am missing that
   breaks the Tonelli factorisation of the a-axis?
5. DEPTH / TERMINATION. The recursion measure is the corank r; rank R ≥ 1 on each chart forces the lower
   corank r−j ≤ r−1 < r. Is corank a sound well-founded measure, or can the rank-stratified recursion
   fail to terminate / revisit the same corank (e.g. if the Schur normal form does not strictly reduce
   the determinantal size)?
6. ANY HOLE. Is there a measure-theoretic gap in "cover {Δ≠0} by r² charts, resolve each chart's rank
   strata recursively, terminate at Morse/monomial leaves" that would make the upper bound FAIL for some
   (r,p) — i.e. a stratum whose contribution diverges below λ_{r,p}?
</questions>

<output_contract>
For each question 1–6: a direct verdict (CORRECT / INCORRECT / NEEDS-CARE) with the precise reason.
Mark clearly which of your statements are PROVEN facts vs your INFERENCE. If you find a hole, give the
smallest (r,p) and the specific stratum where it bites. If the cover is sound, state the single most
fragile step a formaliser should be most careful about. Be concrete and adversarial; do not rubber-stamp.
</output_contract>
