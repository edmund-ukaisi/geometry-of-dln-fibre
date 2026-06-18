<task>
Lean 4 + Mathlib v4.29.0 (toolchain leanprover/lean4:v4.29.0). I need the cleanest proof of
BLOCK-DIAGONAL MATRIX RANK ADDITIVITY, which has NO off-the-shelf lemma in this Mathlib pin
(I grepped: there is no `Matrix.rank_fromBlocks`, no `rank_blockDiagonal`).

Target lemma (CommRing or Field — tell me which is needed):

  theorem rank_fromBlocks_zero_zero
      {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) k) (B : Matrix (Fin c) (Fin d) k) :
      (Matrix.fromBlocks A 0 0 B).rank = A.rank + B.rank

where `fromBlocks A 0 0 B : Matrix (Fin a ⊕ Fin c) (Fin b ⊕ Fin d) k`. (Or stated over the
reindexed `Fin (a+c)`/`Fin (b+d)` — I can reindex with `rank_reindex`/`rank_submatrix` using
`finSumFinEquiv`, those are confirmed to exist.)

CONTEXT — what IS in this Mathlib (confirmed by grep of
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Rank.lean and ToLin.lean):

- `Matrix.rank A := finrank R (LinearMap.range A.mulVecLin)` (the definitional form).
- `Matrix.rank_eq_finrank_range_toLin [Finite m] [DecidableEq n] (A) (v₁ : Basis m R M₁)
   (v₂ : Basis n R M₂) : A.rank = finrank R (LinearMap.range (toLin v₂ v₁ A))`.
- `LinearMap.toMatrix_prodMap [DecidableEq m] [DecidableEq (n ⊕ m)]
   (φ₁) (φ₂) : toMatrix (v₁.prod v₂) (v₁.prod v₂) (φ₁.prodMap φ₂)
              = Matrix.fromBlocks (toMatrix v₁ v₁ φ₁) 0 0 (toMatrix v₂ v₂ φ₂)`
   — note this is the SQUARE / endomorphism version (same basis source and target). I need the
   general rectangular version (a×b and c×d, possibly non-square). Does an analogous
   `toMatrix_prodMap` with FOUR bases `(v₁.prod v₂) (w₁.prod w₂)` exist, or must I derive it?
- `LinearMap.range_prodMap (f) (g) : (f.prodMap g).range = f.range.prod g.range`.
- `Matrix.rank_reindex`, `Matrix.rank_submatrix` (reindex by an Equiv preserves rank).
- `Matrix.rank_one`, `rank_zero` (need `[Nontrivial R]`).

OPEN QUESTIONS I need answered:
1. Is there a `Submodule.finrank_prod` (finrank of `p.prod q : Submodule R (M × M')` equals
   `finrank p + finrank q`) in v4.29, or do I get it via `Submodule.prodEquivOfIsCompl` /
   `LinearEquiv` to `p × q` then `Module.finrank_prod`? Give the EXACT lemma name(s) that exist
   at this pin.
2. The cleanest end-to-end route: is it (a) go through `rank_eq_finrank_range_toLin` with
   `Pi.basisFun` bases + `toMatrix_prodMap` + `range_prodMap` + finrank-of-prod; or (b) work
   directly with `mulVecLin (fromBlocks A 0 0 B)` and show its range is the `prod` of the two
   ranges via `Sum`-pi reindexing (`LinearEquiv.sumArrowLequivProdArrow` /
   `Fintype.piEquivPi`...)? Which has fewer cast/`DecidableEq`/reindex headaches?
3. Watch-outs at this exact pin: `Basis` is `Module.Basis` (bare `Basis` unknown); is the
   rectangular `toMatrix_prodMap` actually present, and what is its name if so?

</task>

<output_contract>
1. State which typeclass (`CommRing` vs `Field`/`DivisionRing`) the additivity lemma genuinely
   needs and why.
2. Give ONE recommended proof route as a concrete Lean proof sketch (tactic skeleton, real lemma
   names at the v4.29 pin), end to end, for `rank_fromBlocks_zero_zero`. Mark any lemma name you
   are INFERRING vs CONFIRMED.
3. Name the exact finrank-of-product lemma(s) that exist (Q1).
4. Note the 2-3 likeliest friction points (casts, DecidableEq, Sum-vs-Fin reindex) and how to
   dodge each.
Be concise. Real lemma names over prose.
</output_contract>

<grounding_rules>
You do NOT have the Mathlib source in front of you; flag every lemma name as CONFIRMED (you are
highly confident it exists at v4.29 with that signature) or INFERENCE (plausible name, verify).
Do not invent a single `rank_fromBlocks`-style lemma and claim it exists — I already grepped and
it does not. If the cleanest route needs a helper I must prove, say so explicitly.
</grounding_rules>
