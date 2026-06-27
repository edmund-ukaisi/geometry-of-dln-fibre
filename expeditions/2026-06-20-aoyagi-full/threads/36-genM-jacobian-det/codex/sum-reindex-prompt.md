<task>
Lean 4 Mathlib v4.29. One stuck goal — the cleanest tactic for a sum-of-squares over a reindexed matrix.

GOAL (after `unfold` + `simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm]`):

  ∑ x, ∑ x_1, (H ((finCongr e0) x) ((finCongr eL) x_1)) ^ 2
    = ∑ i, ∑ j, (H i j) ^ 2

where `H : Matrix (Fin (Wwid 0)) (Fin (Wwid L)) ℝ`, `e0 : Wwid 0 = M ⟨0,_⟩` (so `finCongr e0.symm :
Fin (M⟨0⟩) ≃ Fin (Wwid 0)`... actually the displayed `finCongr` maps the summation index into H's index
type), `eL : Wwid L = M ⟨L,_⟩`. The LHS sums over `x : Fin (M⟨0⟩)`, `x_1 : Fin (M⟨L⟩)`; the RHS over
`i : Fin (Wwid 0)`, `j : Fin (Wwid L)`. The `finCongr`s are bijections, so the double sum is equal
(reindexing a finite sum by a bijection).

I tried `Equiv.sum_comp e g` and `Fintype.sum_equiv` but hit pattern-match failures (the nested double sum
+ both indices reindexed) and `AddCommMonoid` metavariable stuckness when leaving `g` as `_`.

QUESTION: give the SINGLE cleanest tactic block to close this (a nested-sum reindex by two `finCongr`
bijections). Options to rank: (a) `Equiv.sum_comp` applied twice with explicit `g`; (b) `Fintype.sum_equiv`
twice; (c) `Finset.sum_nbij'`/`Finset.sum_bij'` over the product; (d) `Fintype.sum_prod_type` to flatten to
a single sum then one `Equiv.sum_comp` with `Equiv.prodCongr (finCongr e0) (finCongr eL)`; (e) recognizing
`finCongr e0 = Equiv.refl` when `e0` is defeq-`rfl` (is `Wext M 0 = M ⟨0,_⟩` defeq-rfl so `finCongr_refl`
fires, collapsing the whole thing?).

Give the exact Lean tactic lines for the winner, ≤ 12 lines. Note v4.29 lemma names precisely
(`Equiv.sum_comp`, `Fintype.sum_equiv`, `finCongr_refl`, `Fintype.sum_prod_type`, `Equiv.prodCongr`).
Flag any INFERENCE about exact signatures.
</task>
