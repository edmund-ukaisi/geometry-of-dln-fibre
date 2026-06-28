**VERDICT:** (a) is literally impossible for the current bridge: `hPtri` and `hQtri` are statements about the endpoint matrices themselves, not about their action on a residual or their induced Schur reads. Since `Pf 0` is a generic left normalizer, `hNF` does not force `Pf 0` block-lower. The feasible route is a modified (b): construct triangular endpoint frames `P0'`, `Q1'` and pass those to the bridge. But this only proves the bridge for the Score re-keyed to `P0'`,`Q1'`; equality with the old producer-keyed Score is not automatic and is false in general.

For (b), the needed equality would be, for all chart points `w`,
```text
frobSq Schur22( reindex( P0' · (prod(w) - B) · Q1' ) )
=
frobSq Schur22( reindex( Pf0 · (prod(w) - B) · Qf1 ) ).
```
This is **not true from the stated facts**. Reason: if both left frames send the same deepest layer to the same corner, then `Pf0 = U · P0'` with `U = [[I, *], [0, *]]`; dually `Qf1 = Q1' · V` with `V = [[I, 0], [*, *]]`. These are precisely the non-triangular directions that can change the `(2,2)` Schur complement of a general residual. The obstruction is leakage through the free `U12` and `V21` blocks. Normalising the deepest point only fixes the action on the corner matrix, not the Schur complement of nearby residuals.

Minimal facts needed:

- To build `P0'`: tail-cols-zero for `deepestPoint 0`, `deepestPoint_leadingBlock_isUnit`, and `blockLower_left_normalizer`.
- To prove `P0'` normalises layer 0: the block identity
  `P0' · [[A11,0],[A21,0]] = [[I,0],[0,0]]`.
- To build `Q1'`: tail-rows-zero / the dual leading-block invertibility information for layer 1, plus `blockUpper_right_normalizer`; `hcorner` can supply the producer-side corner normalisation but does not by itself make `Qf1` upper.
- To discharge `hPtri`, `hQtri`: only the constructed normalizer shapes.
- To identify the old and new Scores: an extra assumption is needed, e.g. `Pf0 = P0'` and `Qf1 = Q1'`, or enough residual restrictions making the free leak blocks invisible. The stated bundle facts do not give this.

Proof sketch:

1. Write `deepestPoint 0` in corner blocks as `[[A11,0],[A21,0]]` with `A11` invertible. Define
   `P0' = [[A11⁻¹,0],[-A21 A11⁻¹,I]]`. Then `P0'` is block-lower and sends this matrix to `corM`.

2. Dually write the last layer in tail-rows-zero form and use the right block-upper normalizer to get `Q1'` block-upper with `deepestPoint 1 · Q1' = corM`.

3. Since `P0'` is block-lower and `Q1'` is block-upper by construction, the bridge hypotheses `hPtri` and `hQtri` are discharged.

4. Compare with the producer frames. From `Pf0 · deepestPoint 0 = corM = P0' · deepestPoint 0`, we only get `Pf0 = [[I,*],[0,*]] · P0'`. From `deepestPoint 1 · Qf1 = corM = deepestPoint 1 · Q1'`, we only get `Qf1 = Q1' · [[I,0],[*,*]]`. The free `*` blocks are not killed by `hNF` or `hcorner`.

5. Therefore the old producer-keyed Score and the triangular-keyed Score agree only under an additional invariance/vanishing hypothesis. They are not equal as a block-algebra consequence of the given bundle.

Landmines: the `- B` shift matters because the comparison is about residuals, not only the deepest corner matrix. The `+1` in `(toBlocks₁₁ + 1)⁻¹` does not rescue the argument; Schur complements are still sensitive to upper-left/right-lower conjugations. The corner-split reindex must be fixed consistently, otherwise the block-lower/block-upper statements are not even about the same decomposition.