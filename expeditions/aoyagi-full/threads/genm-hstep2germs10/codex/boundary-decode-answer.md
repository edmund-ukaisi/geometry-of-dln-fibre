**VERDICT:** The plan is sound in outline, but Step A is the part I would demote. It should go through only with the exact reindex orientations checked locally: the identity
`P * reindex e_r.symm e_c.symm M = reindex e_r.symm e_c.symm (Pt * M)`
is a `submatrix_mul_equiv`/reindex-mul statement, not a simp fact. Step C also needs the lower-frame facts transported from `Pt` to `psiFrame0`; `Pf` being a unit is not by itself enough unless you already have `IsUnit psiFrame0.toBlocks₁₁`.

For Step B, choose **(i) whole-matrix**. Prove one chain-width expansion lemma:
```lean
deepestChain (framedParamsPivot q) firstLayer
  = fromBlocks 1 0 0 0 + psiFrame0 * psiGhat q firstLayer
```
or the corresponding version before substituting `q = psiSplitRawGen q0`.

Use these Mathlib lemmas/tactics as the spine: `Matrix.submatrix_mul_equiv`, `Matrix.submatrix_submatrix`, `Matrix.reindex_apply`, `Matrix.submatrix_apply`, `Matrix.ext`, plus simp lemmas for `submatrix_add`/`reindex` if available locally. Then prove the composite split maps by:
```lean
ext i j <;> cases i <;> cases j <;>
  simp [Matrix.reindex, Matrix.submatrix_submatrix,
        rThr_finCongr_split_inl, rThr_finCongr_split_inr]
```
Exact simp lemma names around `reindex` may need local checking, but `Matrix.submatrix_mul_equiv` and `Matrix.submatrix_submatrix` are the right Mathlib route. Block-by-block is only a fallback; it repeats the same cast proof four times and makes zero/one blocks noisier.

Simpler overall route: avoid Step A as a standalone H-width lemma. Expand `deepestChain`, `deepestChainLayer`, `framedParamsPivot`, and `framedLayer`, then push the outer chain reindex through the product directly. This gives the chain-width equation where `psiFrame0` and `psiGhat` naturally live.

Traps: keep `Ring.inverse` consistent with the banked lemma; use `Ring.mul_inverse_cancel` on the exact `IsUnit psiFrame0.toBlocks₁₁`. Do not mix H-width reads with `movedC firstLayer` before transporting to chain-width. After the forced decode lemma gives `psiFrame0 * psiGhat = fromBlocks D.toBlocks`, finish with `Matrix.fromBlocks_toBlocks`, then `abel` for `I + (M - I) = M`.