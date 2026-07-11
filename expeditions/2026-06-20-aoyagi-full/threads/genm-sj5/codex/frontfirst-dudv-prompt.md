<task>
I am reviewing a formalised measure-theory bound for the RLCT of deep linear networks (Aoyagi §5,
front-first "coupled two-block radial" majorant). Independent decorrelated check of ONE thing: the
du/dv role assignment (which block dimension carries which weight) feeding a radial integral lemma.
Do NOT trust my framing; derive the correct assignment from scratch, then compare.

SETUP (exact).
- A0 is a real m×r matrix ("front factor"). P is a real r×n matrix ("tail"). Front loss = squared
  Frobenius norm frobSq(A0·P) = ‖A0·P‖_F^2.
- Diagonalise the Gram G = P·Pᵀ (r×r, symmetric PSD): G = U·diag(λ)·Uᵀ, U orthogonal, λ_1..λ_r ≥ 0
  the eigenvalues. Then the identity frobSq(A0·P) = Σ_{j=1..r} λ_j · ‖(A0·U)_{·j}‖^2, where
  (A0·U)_{·j} is the j-th COLUMN of A0·U (a vector of m entries, one per row i∈{1..m}).
- One eigen-index c is the "collapse" index = argmin_j λ_j, and λ_c = (σ_min P)^2 =: σ^2 (the small
  singular value). The remaining r−1 indices j≠c are the "stable" block; on the working region ("sector")
  every stable eigenvalue satisfies λ_j ≥ κ^2 (κ a fixed O(1) constant).
- Lower bound used: frobSq(A0·P) ≥ σ^2·‖(A0U)_{·c}‖^2 + κ^2·Σ_{j≠c} ‖(A0U)_{·j}‖^2.

INTEGRAL LEMMA (the one being fed). A separate lemma `twoBlock_radial_le` is stated over a Euclidean
product ball with two blocks u∈ℝ^{du}, v∈ℝ^{dv}, integrand (κ^2·‖u‖^2 + σ^2·‖v‖^2)^{−c'}, and
concludes ∫ ≤ C·σ^{−α'} with a FINITE C provided max(0, 2c'−du) < α' < dv. Note in THIS lemma: the
weight κ^2 multiplies the du-block ‖u‖^2, and the weight σ^2 multiplies the dv-block ‖v‖^2; the
output exponent bound σ^{−α'} and the constraints use du in the lower threshold and dv in the upper.

QUESTIONS.
1. Reconstruct the two blocks of the lower-bound quadratic form as Euclidean vectors. What is the
   total real dimension of (i) the collapse block ‖(A0U)_{·c}‖^2 and (ii) the stable block
   Σ_{j≠c}‖(A0U)_{·j}‖^2, expressed in m and r? Which scalar weight (σ^2 vs κ^2) multiplies each?
2. To feed `twoBlock_radial_le` (integrand κ^2‖u‖^2 + σ^2‖v‖^2, thresholds 2c'−du < α' < dv), what
   MUST du and dv be, in m and r? State the resulting threshold on α' in m,r,c'.
3. If someone instead set du = (collapse-block dim) and dv = (stable-block dim), i.e. swapped, what
   would go wrong — would it (a) fail to type-check, (b) type-check but give a WRONG/false threshold,
   or (c) be harmless? Explain concretely.
4. Independent sanity: for the paper's (3,3,3,4) example the intended numbers are m=3, r=3, giving one
   block of dimension 6 and one of dimension 3. Which is which (weight + dimension), and what is the
   admissible α' window at the borderline c'=3?
</task>

<output_contract>
Four numbered answers, terse. For Q1/Q2 give explicit formulas in m,r. For Q3 pick (a)/(b)/(c) and
justify in 2–3 sentences. For Q4 give the two (weight, dimension) pairs and the α' interval at c'=3.
End with a one-line VERDICT: is "du = m·(r−1) with weight κ², dv = m with weight σ²" the correct
(non-swapped) assignment? YES/NO.
</output_contract>

<grounding_rules>
Derive from the stated identity; do not assume my assignment is right. If any step is an inference
rather than a forced consequence of the setup, mark it "(inference)". Flag any hidden assumption
(e.g. about how many collapse directions there are) explicitly.
</grounding_rules>
