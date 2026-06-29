**1. Verdict**

Yes: genm-mapeq’s fix is the right shape, not over-engineered. From your summary, `Matrix.BlockTriangular.det` uses one grading `b : Fin N → α` for both row and column indices. Your proved vanishing is instead two-graded:

`rowLayer i < colLayer j` implies the relevant entry vanishes.

So some identification of the row-layer indexing with the column-layer indexing is forced before `BlockTriangular.det` can see the hypothesis. The relabel `e : Fin N ≃ FlatIdx` is exactly that identification.  
ASSUMPTION: the intended determinant factorization is by the paper’s actual layers, not by a coarser artificial grading.

**2. Lighter Routes**

(a) From your summary, `BlockTriangular.det` is strictly single-grading. A custom two-grading theorem could be written, but it would still need layerwise row-fibre/column-fibre equivalences to define square diagonal-block determinants. That is the same data as `e`, just hidden inside a more general theorem.

(b) A row permutation `σ : Fin N ≃ Fin N` can align the gradings, but it is just `e` in disguise: with `rFlat := equivFin FlatIdx`, take `σ = e.trans rFlat.symm`. Conversely, any such `σ` gives `e = σ.trans rFlat`. A same-permutation conjugation `M.submatrix σ σ` is not generally enough, because it permutes columns too; precomposing both gradings by the same bijection cannot make genuinely different layer functions equal. Row-only or separate row/column permutations work up to sign/unit, but are not lighter.

(c) Absorbing the relabel into `Q_M` is genm-mapeq’s fix. There is no direct “chartIdxEquiv-as-flat-equiv” because `ChartIdx` and `FlatIdx` are different types. You can hide the construction behind `Classical.choose`, but the per-layer cardinality/equivalence proof still exists. Rank: the fibre-bijection `e` is unavoidable up to packaging.

**3. Recommendation**

Deep-fill the genm-mapeq formulation: isolate one noncomputable layer-compatible relabel `e`, prove the single lemma that its FlatIdx layer equals the `chartIdxEquiv` layer, define `Frame_M` using that relabel, and keep `Q_M` as the determinant-unit outer factor.

The one risk is Lean bookkeeping: opaque `Fintype.equivFin`s plus casts across `Fin L` layer equalities may make simp brittle. Keep the compatibility lemma explicit and use it as the only gateway.