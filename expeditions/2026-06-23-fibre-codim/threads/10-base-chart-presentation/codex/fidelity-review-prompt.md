<task>
I am doing a FIDELITY review of a Lean 4 / Mathlib formalisation. I need a decorrelated
second opinion on whether the Lean STATEMENT faithfully captures the intended INFORMAL claim.
Do NOT check the proof; assume the build is green and axiom-clean. Judge the statement only.

INFORMAL CLAIM (target):
Over a field k, on the pivot chart where the top-left r×r block Δ of a block matrix
M = [[Δ, B12],[B21, B22]] is invertible, M has rank EXACTLY r  iff  the Schur complement
vanishes, i.e. B22 = B21·Δ⁻¹·B12. This gives a bijection
  Mat^{rk=r} ∩ U  ≅  GL_r × Mat_{r×(q−r)} × Mat_{(p−r)×r}
of dimension δ = r(p+q−r), where M is p×q (p rows, q cols), r the pivot size.

The Lean (Mathlib v4.29 conventions). `Matrix.fromBlocks A B C D` builds
[[A,B],[C,D]] over index (n⊕o) rows, (l⊕m) cols (A: n×l top-left, B: n×m top-right,
C: o×l bottom-left, D: o×m bottom-right). `Matrix.rank A = finrank (range A.mulVecLin)`
(column rank over a field). `⅟Δ` is the genuine two-sided inverse from `[Invertible Δ]`.

HEADLINE 1:
  theorem rank_fromBlocks_eq_card_iff_schur
    (Δ : Matrix m m k) (B12 : Matrix m n k) (B21 : Matrix l m k) (B22 : Matrix l n k)
    [Invertible Δ] :
    (fromBlocks Δ B12 B21 B22).rank = Fintype.card m  ↔  B22 = B21 * ⅟Δ * B12

HEADLINE 1' (inverse form, under IsUnit Δ.det, using Matrix.inv `Δ⁻¹`):
  same iff with RHS  B22 = B21 * Δ⁻¹ * B12.

CHART + PARAMETRIZATION:
  pivotRankChart k m l n := {M : Matrix (m⊕l) (m⊕n) k | M.rank = Fintype.card m ∧ IsUnit M.toBlocks₁₁.det}
  pivotRankChartEquiv : {M // M ∈ pivotRankChart k m l n} ≃
       {Δ : Matrix m m k // IsUnit Δ.det} × Matrix m n k × Matrix l m k
  M ↦ (toBlocks₁₁ M, toBlocks₁₂ M, toBlocks₂₁ M); inverse (Δ,B12,B21) ↦ fromBlocks Δ B12 B21 (B21·Δ⁻¹·B12).

DIMENSION:
  finrank k (Matrix m m k × Matrix m n k × Matrix l m k)
      = card m * card m + card m * card n + card l * card m  (the affine PARAMETER space)
  and arithmetic lemma: r*r + r*(q−r) + (p−r)*r = r*(p+q−r) for r≤p, r≤q.
  The card EXPLICITLY DEFERS "chart variety dimension = parameter-space dimension" (needs the
  AG step: a Zariski-open subset has the dimension of its ambient space).
</task>

<output_contract>
Answer these 7 numbered points, each in ≤3 sentences, verdict-first (OK / MISMATCH / OVERCLAIM):

1. SCHUR SIGN/ORDER. Schur complement of [[Δ,B12],[B21,B22]] is S = B22 − B21·Δ⁻¹·B12.
   Does "S = 0 ⟺ B22 = B21·Δ⁻¹·B12" hold with the EXACT factor order B21·Δ⁻¹·B12 (not Δ⁻¹
   sandwiched differently, not B12·Δ⁻¹·B21)? Confirm dimensions compose (B21: (p−r)×r, Δ⁻¹: r×r,
   B12: r×(q−r) → (p−r)×(q−r) = shape of B22). 

2. RANK = r EXACTLY. Is "rank = card m" the right RHS for "rank exactly r"? With Δ invertible
   (rank Δ = r), is it standard that rank M = r ⟺ Schur complement = 0 (i.e. M cannot have rank
   < r when its top-left r×r block is already full rank r, so "= r" coincides with "≤ r")? Any
   edge case where rank M = card m but Schur ≠ 0, or vice versa?

3. INDEX→DIMENSION MAP. The Lean uses index types m (size r), l, n. M is (m⊕l)×(m⊕n), so
   p = r + card l, q = r + card n. Then B12: r×(card n)=r×(q−r) ✓, B21: (card l)×r=(p−r)×r ✓.
   Does the codomain {Δ//IsUnit det} × Matrix m n k × Matrix l m k faithfully read as
   GL_r × Mat_{r×(q−r)} × Mat_{(p−r)×r}? Flag any transposition (e.g. B21 stored as l×m = (p−r)×r, correct?).

4. IFF NON-VACUITY. Is the iff genuinely two-sided content (not vacuously true)? Could
   [Invertible Δ] secretly force B22 = B21·⅟Δ·B12 regardless, making one direction trivial?

5. CHART FIDELITY. Does pivotRankChart = {rank = card m ∧ top-left det a unit} faithfully encode
   "exact-rank-r locus ∩ pivot chart U"? Is requiring `IsUnit toBlocks₁₁.det` equivalent to "Δ ∈ GL_r"?

6. DIMENSION HONESTY. Given the card explicitly DEFERS variety-dim = param-dim (AG openness), is
   it correct to say the module proves a PARAMETER-SPACE finrank identity (= δ) and an arithmetic
   identity, but NOT a variety-dimension theorem? Is deferring the openness step the right scope, or
   is there a cheaper honest route to the variety dim that's being missed?

7. NAMING/OVERCLAIM. Do these names overclaim?
   - rank_fromBlocks_eq_card_iff_schur (states an iff about rank = card)
   - pivotRankChartEquiv (an Equiv of types / k-points)
   - finrank_pivotRankChart_params (finrank of the PARAMETER space, name says "params")
   - dim_params_eq_delta (arithmetic)
   Flag any name that reads as more than what's described.
</output_contract>

<grounding_rules>
This is pure statement-fidelity math review; you have the full statements above. Distinguish
"standard textbook fact" from "I'd want to double-check." If you assert a sign/order or a rank
fact, state the one-line reason (e.g. Guttman rank additivity / Schur). Flag inference vs fact.
</grounding_rules>
