<task>
Lean 4 + Mathlib. A block-triangular-determinant route has a GRADING SHAPE issue I need adjudicated —
is genm-mapeq's fix the intended one, or is there a lighter route? Facts (verified by reading code):

THE MAP: `phi : (Fin N → ℝ) → (Fin N → ℝ)`, `phi = paramsEquivFlat ∘ chartParamsGen`. I want its
Fréchet-derivative matrix `Dphi : Matrix (Fin N) (Fin N) ℝ` (= LinearMap.toMatrix' of fderiv) to be
BLOCK-TRIANGULAR under a single layer grading, so `Matrix.BlockTriangular.det` gives det = ∏ diagonal-
block dets.

THE SHAPE ISSUE: the matrix's ROW index (output) and COLUMN index (input) carry DIFFERENT gradings:
- INPUT (columns): `x : Fin N` is decoded by `chartIdxEquiv : Fin N ≃ ChartIdx`, where
  `ChartIdx = Σ k : Fin L, Fin (schurDim k) ⊕ Fin (liftDim k)`. Layer of column q = `(chartIdxEquiv q).1 : Fin L`.
- OUTPUT (rows): produced by `paramsEquivFlat : Params ≃ (Fin N → ℝ)`, whose flat index is
  `FlatIdx = Σ q : (Σ s : Fin L, Fin (M s.castSucc)), Fin (M q.1.succ)`. Layer of row i = `(equivFin FlatIdx i).1.1 : Fin L`.
- The two `Fin N ≃ {layer-graded Σ-type}` bijections are SEPARATE `Fintype.equivFin`s (Classical, opaque,
  on DIFFERENT index types ChartIdx vs FlatIdx). So row-grading ≠ col-grading. `Matrix.BlockTriangular M b`
  needs ONE `b : Fin N → α` for both → can't apply directly.
- BUT: the PROVEN off-block-vanishing fact (sorry-free) is "output layer s reads only INPUT layers ≤ s"
  (a two-grading statement: output-layer via paramsEquivFlat-side, input-layer via chartIdxEquiv-side).
- The per-layer cardinalities MATCH: #(ChartIdx layer-s slots) = schurDim s + liftDim s = M(s.castSucc)·M(s.succ)
  = #(FlatIdx layer-s slots) (banked: roleSquare_eq + chartDim_eq_flatDim). So a layer-preserving bijection
  ChartIdx ≃ FlatIdx exists.

genm-mapeq's FIX: choose `e : Fin N ≃ FlatIdx` LAYER-COMPATIBLE with chartIdxEquiv (e q has the same Fin-L
layer as (chartIdxEquiv q).1), built as chartIdxEquiv ∘ (per-layer fibre bijection ChartIdx ≃ FlatIdx).
Then redefine `Frame_M := (flatEquivOf e).symm (chartParamsGen …)` (output relabeled by e), so BOTH row
and col are graded by the SAME `bLayer = (chartIdxEquiv ·).1`; `Q_M = paramsEquivFlat ∘ (flatEquivOf e).symm`
(a relabel, |det|=1, the outer factor absorbing the mismatch). The block-tri then uses ONE bLayer.
</task>

<output_contract>
Answer in 3 short sections:

1. Is genm-mapeq's layer-compatible-e fix the RIGHT shape (correct + minimal), or is it over-engineered?
   Specifically: does Matrix.BlockTriangular genuinely require row-grading = col-grading (a single b : Fin
   N → α), forcing SOME identification of the two layer-gradings (hence the relabel e)?

2. THE LIGHTER-ROUTE QUESTION: is there a route AVOIDING the per-layer fibre bijection? Candidates:
   (a) A TWO-GRADING block-triangular det: does Mathlib have a block-triangular det for a matrix whose row
       and col index types DIFFER but are both graded (a "generalized block-triangular" / a det via a
       triangular structure over a product/relabeled index)? Or is BlockTriangular.det strictly single-grading?
   (b) Conjugate the matrix by a PERMUTATION that aligns the gradings (det_submatrix_equiv_self, like the
       pivotBlowupOnDeriv_det Equiv.swap pattern) — does a single permutation σ : Fin N ≃ Fin N suffice to
       make σ-conjugated Dphi block-tri under ONE grading, WITHOUT building the full ChartIdx≃FlatIdx fibre
       bijection? (det_submatrix_equiv_self preserves det.) Is σ = (the relabel composed) — i.e. is option
       (b) just genm-mapeq's e in disguise, or genuinely lighter?
   (c) Define the chart's output grading to BE the input grading by composing paramsEquivFlat with the
       relabel ONCE at the Q_M (det-1) factor — which is genm-mapeq's fix. Is there a way to make Q_M absorb
       the relabel WITHOUT explicitly constructing e (e.g. Q_M = paramsEquivFlat ∘ chartIdxEquiv-as-flat-equiv
       directly, reusing chartIdxEquiv's OWN equivFin)?
   Rank: is the fibre-bijection e unavoidable, or does (b)/(c) give a lighter shape?

3. The SINGLE cleanest formulation (your recommendation) for genm-mapeq to deep-fill, + the one risk.
</output_contract>

<grounding_rules>
Only my summary. Mark unstated-fact dependencies "ASSUMPTION: …". Distinguish "follows from your summary"
vs "verify X". No Lean code blocks >5 lines.
</grounding_rules>
