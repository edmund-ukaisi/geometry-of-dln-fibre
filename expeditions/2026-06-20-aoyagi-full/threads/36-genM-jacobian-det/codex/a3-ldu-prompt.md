<task>
Lean 4 + Mathlib v4.29.0. Phase A3 of a Jacobian-determinant engine. I have already landed (sorry-free):
- A1: det of left-mult-by-K on Matrix (Fin t)(Fin c) ℝ = K.det^c; right-mult = K.det^r.
- A2 keystone: a 2-block lower-triangular endo helper `lowerTri f g h : M×N →ₗ M×N`, (m,n)↦(f m, g n + h m),
  with `lowerTri_det : det = f.det * g.det` (via LinearMap.det_eq_det_mul_det on Submodule.snd).
- The Schur-frame differential det |det DS| = |K.det|^(r+c), assembled as a 3-fold lowerTri nest.

A3 GOAL. The LDU-core parametrization Jacobian. Parametrize a t×t real matrix K by (L_free, q, U_free):
L unit-lower-triangular (free strictly-lower entries), D = diag(q_0..q_{t-1}), U unit-upper-triangular
(free strictly-upper entries); the map sends params ↦ entries of K = L·D·U. #params = t(t-1)/2 + t +
t(t-1)/2 = t^2 = #entries (square chart). VERIFIED in sympy:
  t=1: |det J| = 1 ; t=2: |det J| = q0^2 ; t=3: |det J| = q0^4 q1^2.
So |det J| = ∏_{i=0}^{t-1} |q_i|^{2(t-1-i)}. The (3,3,3,3) hand instance proves the t=2 case
(`Kparam3333Deriv_det = (x1)^2`) by realizing the differential as a Matrix, proving
`Matrix.BlockTriangular OrderDual.toDual` (lower-triangular), then `Matrix.det_of_lowerTriangular`
and a `Fin.prod_univ_succ` over the diagonal — but that is hand `fin_cases` at fixed t=2.

CONSTRAINTS / what I want.
The achiever chart evaluates the LDU core at a SPECIFIC achiever point; the differential I need is the
Frechet derivative of `(L_free, q, U_free) ↦ L D U` at a point. The det is `∏ q_i^{2(t-1-i)}` regardless
of the L,U,q point values (it depends only on q). I need a clean, OPAQUE-t Lean theorem
`lduCore_det : |det (lduCoreDeriv ...)| = ∏ i, |q i|^(2*(t-1-i))`.

Two routes:
 (a) ABSTRACT via lowerTri/prodMap: can the LDU differential be expressed as a nest of lowerTri /
     scalar-block maps so its det telescopes WITHOUT an explicit Matrix + index arithmetic? The diagonal
     blocks would have to be "scale row/col i by q_i" maps. Is there a clean decomposition?
 (b) EXPLICIT Matrix + Matrix.BlockTriangular over a Fin (t*t) (or (Fin t × Fin t)) grading at opaque t,
     proving the strictly-upper entries vanish by INDEX ARITHMETIC (not fin_cases), then
     det_of_lowerTriangular + a Finset.prod over the diagonal = ∏ q_i^{2(t-1-i)}.

QUESTIONS.
1. Which route is cleaner/more robust at OPAQUE t in Lean v4.29? Be decisive.
2. For the chosen route give the precise lemma chain (named Mathlib lemmas) and the differential's
   definition shape. Crucially: what is the cleanest way to DEFINE the LDU parametrization differential
   as a LinearMap so its det is computable? (The hard part is the param space ↔ matrix-entry indexing
   and the strictly-lower L / strictly-upper U free-entry bookkeeping at opaque t.)
3. Is there an existing Mathlib lemma for the det of the LDU/Bruhat parametrization Jacobian, or for
   "scale-row-i-and-col-i-by-q_i" maps? (e.g. anything around Matrix.transvection, diagonal conjugation,
   or det of the map A ↦ D A or A ↦ D A D)? Flag VERIFY if unsure.
4. Honest assessment: is A3 a "few-lemma S-size" build or a substantial bespoke index-arithmetic build?
   The design rated it "Size S / easy" — do you agree, and if not where is the real cost?
</task>

<output_contract>
1. Route choice (a) or (b), one paragraph, decisive.
2. The lemma chain + the LinearMap definition shape for the chosen route. Concrete.
3. Q3 answer: named lemma or "no, build it". Flag VERIFY for any uncertain name.
4. Q4 honest size assessment, one paragraph, and the single biggest risk.
Terse. Name only lemmas you are confident exist in v4.29.
</output_contract>

<grounding_rules>
Flag any lemma name you are NOT sure exists in v4.29 as "VERIFY". Distinguish "exists" (fact) from
"should work" (inference). Do not invent signatures.
</grounding_rules>
