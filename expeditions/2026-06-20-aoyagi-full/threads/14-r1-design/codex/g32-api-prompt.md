<task>
Design the LEAN 4 / Mathlib v4.29 API for the "matrix-chain Schur-complement reduction" lemma (G3.2),
the crux of a general-M deep-linear-network RLCT resolution. I need the STATEMENT shape pinned (not the
proof) — specifically the hypotheses and the conclusion's regularity claims, where there are subtle
choices. This will be built on, so getting the API right matters more than speed.

MATH SETUP (matrix chain):
- A chain C = (C^(1),…,C^(L)), C^(s) : Matrix (Fin (M s)) (Fin (M (s+1))) ℝ (sizes M : Fin (L+1) → ℕ).
- The chain product ∏C : Matrix (Fin (M 0)) (Fin (M L)) ℝ.
- The loss is ‖∏C − B‖²_Frobenius at B=0 (deepest rank-r stratum); RLCT is LOCAL at the origin.

THE PROTOTYPE (already proven, L=1 single matrix), `block_elimination`:
  theorem block_elimination (H : Fin (L+1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (hB : B.rank = r) : ∃ (P : Matrix .. ℝ) (Q : Matrix .. ℝ), IsUnit P ∧ IsUnit Q ∧
      P * B * Q = Matrix.of (fun i j => if i=j ∧ i<r then 1 else 0)
  — i.e. units P,Q with P·B·Q = diag(E_r, 0). NO chart, GLOBAL units (it's a single matrix, constant rank).

THE G3.2 TARGET (the CHAIN generalization), per the design doc:
  In a PIVOT CHART where the leading t×t minor of the partial product is a UNIT (invertible), there are
  UNIMODULAR row/column changes Q^(s) with ∏(Q^(s) C^(s) Q^(s+1)) = [[E_t (reg), 0],[0, ∏C']],
  C'^(s) the REDUCED chain (sizes (M^s−δ_s)×(M^{s+1}−δ_{s+1})), and ‖∏C−B‖² = ‖reg‖² + ‖∏C'‖² (additivity, L2/S1.5).
  ⟹ rlctAt reduces to ½·(reg-dim) + rlctAt(‖∏C'‖²); recurse on C'.

THE SUBTLETY I VERIFIED (sympy, L=1): the Schur complement is D − C·A⁻¹·B with A the t×t unit pivot.
So the unimodular changes are L=[[I,0],[−CA⁻¹,I]], R=[[I,−A⁻¹B],[0,I]] (det 1) — but they carry A⁻¹,
i.e. the PIVOT IN THE DENOMINATOR. They are polynomial ONLY where A is a unit (the chart). So "Q^(s)
unimodular polynomial-entry" from the doc is imprecise: the Q's are ANALYTIC over the unit-locus
(rational with the unit pivot as denominator), det = ±1 (or ±unit). This is the chart-LOCAL caveat
(RLCT is local; the pivot coordinate is a blow-up exceptional, nonzero on the chart).

MY QUESTIONS (API design, Lean-specific):
Q1. How should the Q^(s) regularity be stated? Options:
   (a) IsUnit Q^(s) (over the matrix ring ℝ-entries) — but then Q's entries are A⁻¹-rational, fine if
       A is a unit SCALAR/block, since Matrix.IsUnit ⟺ IsUnit det, and det=±1. But the ENTRIES carry A⁻¹.
   (b) Q^(s) as matrices over the localized ring / over a chart neighborhood where the pivot is a unit.
   (c) Avoid the inverse: state it as ∃ Q (units) such that Q·(∏C)·Q' = block form, WITHOUT exposing
       the per-factor Schur — i.e. the CHAIN-PRODUCT block-diagonalizes (like block_elimination but the
       reduction respects the chain factorization). Is the per-factor Q^(s) even needed, or does the
       recursion only need ∏C ~ diag(E_t, ∏C') as a PRODUCT (units on the two ends)?
   Which is the cleanest Lean statement that (i) is provable reusing block_elimination, (ii) feeds the
   RLCT recursion (the additivity ‖∏C−B‖²=‖reg‖²+‖∏C'‖² + the rlctAt split)?
Q2. Is the per-factor unimodular Q^(s) actually REQUIRED, or is the load-bearing claim just:
   "∏C = U · diag(E_t, ∏C') · V for end-units U,V (analytic on the chart), with ∏C' a chain product of
   the reduced dims"? For the RLCT recursion (S1 invariance under analytic units + the L2/S1.5
   additivity), I believe only the END-form (U·blockform·V) + ‖·‖²-additivity is needed, NOT the
   per-factor changes. Confirm: does the recursion need the per-factor Q^(s), or only the end-unit
   block-diagonalization of the PRODUCT? (This drastically simplifies the Lean statement.)
Q3. For the RLCT-recursion to close, the key is: rlctAt(‖∏C−B‖²) at 0 = ½·reg-dim + rlctAt(‖∏C'‖²) at 0.
   This needs S1 (analytic-unit invariance of rlctAt) + S1.5 (smooth-block additivity, DONE) +
   product_reduction (DONE for fixed M). Which of these consumes the block-diagonalization, and in what
   form (end-units vs per-factor)? What's the minimal Schur-lemma conclusion that product_reduction/S1.5
   can consume?
Q4. The dimension bookkeeping (δ_s, reduced sizes M^s−δ_s, Fin (M^s − δ_s) casts): in Lean this is
   painful (Fin-arithmetic + Matrix reindexing + the partial-product associativity). Recommend the
   cleanest representation of "the reduced chain C'" — a new chain over reduced sizes, or a submatrix
   block of the original via Fin.castLE / Matrix.submatrix? Which minimizes the Fin-cast friction across
   the recursion?
</task>

<output_contract>
Answer in 4 sections (Q1–Q4). For each: the RECOMMENDED Lean statement shape (signature sketch, not full
proof), the tradeoff, and any soundness trap. Be concrete about: end-units-vs-per-factor (Q2 is the
pivotal simplification — rule on it decisively), the Fin-dimension representation (Q4), and what the
RLCT recursion actually consumes (Q3). Flag if the "polynomial-entry Q" in the design doc is a real
soundness issue vs a fixable wording (my read: fixable — analytic-on-chart, det ±1).
</output_contract>

<grounding_rules>
The L=1 Schur algebra is given + sympy-verified — reason from it concretely. Distinguish what's
PROVABLE-reusing-block_elimination from what needs new machinery. Flag inference vs fact. The goal is
the minimal sound API that feeds the existing RLCT recursion (S1/L2/S1.5/product_reduction), not a
maximal restatement of Aoyagi.
</grounding_rules>
