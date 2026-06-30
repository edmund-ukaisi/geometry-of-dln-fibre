**Summary**
- Reduce J11 to evaluating `chainAFDeriv` on `d := eIn.symm (0, (v1, PUnit.unit))` and transporting through `rowSplitLE`/`prodComm`.
- Align the `rowSplitLE` row permutation with `finSplit` via a dedicated lemma so that block extractions become `simp`.
- Use the linearity of the `matrixReaderCLM` pieces plus `eIn` inverse formulas to read off `dN d = 0`, `dW d = v1.1`, and `dC d = v1.2`, completing the `chainUnitMap` comparison.

**Q1 – Skeleton for the derivative**
- `reindexL1` bridge: package the entrywise equality between `BparamsLeaf ha z 1` and `chainA ... (readN ⟨0⟩ z) (readW ⟨0⟩ z) (rfinDirect ha z)` into a lemma `reindexL1_BparamsLeaf_eq`. Prove once using `simp`/`funext` on matrix coordinates.
- Differentiability: apply `hasFDerivAt_chainA` with the concrete `Nf`, `Wf`, `Cf`. Combine with `continuousLinearMap.compHasFDerivAt` (or `map_hasFDerivAt_equiv`) for the `reindexL1` equivalence, yielding a lemma
  ```
  hasFDerivAt_reindexL1 :
    HasFDerivAt (fun z => reindexL1 ha (BparamsLeaf ha z 1))
      (chainAFDeriv ... (readN ⟨0⟩) (readW ⟨0⟩) ...) y₀
  ```
- Peel off `fderiv`: once the `HasFDerivAt` lemma is in place, use `hasFDerivAt.fderiv` to convert to equality in `continuousLinearMap`. Transport across the linear equivalence with `reindexL1.toLinearIsometryEquiv.toContinuousLinearEquiv`.
- Block extraction: prove a helper
  ```
  lemma rowSplitLE_apply (M : Matrix _ _) :
    rowSplitLE ha (reindexL1_inv?? M) = (M ∘ keptIndex, M ∘ liftIndex)
  ```
  or directly:
  ```
  lemma rowSplitLE_chainAFDeriv
    : rowSplitLE ha (chainAFDeriv h ...) =
        (dWCLM, dCMinusCLM)
  ```
  by unfolding `rowSplitLE` (it is a `LinearEquiv` built from `finSumFinEquiv` composed with `sumArrowLequivProdArrow`) and matching the matrices entrywise with `simp` using `Fin.sum_unapply`, `Finset.univ_unique`, and `Matrix.submatrix`. This isolates the block corresponding to `Fin schurT1` and the complement; `finSplit` vs `finSumFinEquiv` disagree only by the `Fin.cast` induced by `schurT1 + schurC1 = Wext1`, so the proof reduces to rewriting indices with `Fin.cast` lemmas.
- After that lemma, combine
  ```
  (packLayer1 ha (fderiv ... d))
    = prodComm _ (rowSplitLE _ (_)) = (lift-block, kept-block)
  ```
  yielding the desired `(v1.1, v1.2 - readN⟨0⟩·v1.1)` once the directional evaluations from Q2 are inserted.

**Q2 – Directional evaluation**
- `dN`: because `readN ⟨0⟩` reads a V0 slot, `matrixReaderCLM` applied to `d` collapses to `slotReadV0 d` for that slot. Use the existing lemma `slotReadV0_fderiv_apply` at the direction level:
  ```
  have hV0 : slotReadV0 d = 0 := by
    simpa using congrArg slotReadV0 (eIn_left_inv _)
  ```
  Then rewrite `dN d` through `slotReadV0` and `matrixReaderCLM` with `simp`.
- `dW` and `dC`: leverage the inverse equations already banked for `eIn`, e.g.
  ```
  have : (eIn ha δ).2.1 = _
  ```
  invert it:
  ```
  have hLift := congrArg Prod.fst (eIn_symm_apply ha _ _) -- yields W block
  have hLeaf := congrArg Prod.snd ...
  ```
  Combined with the linearity of `matrixReaderCLM`, deduce
  ```
  dW d = v1.1
  dC d = v1.2
  ```
  using `wToMat`/`leafToMat` inverses (`wToMat_inv_apply`, `leafToMat_inv_apply`) and `simp` with `Matrix.of_apply`.
- These substitutions collapse `chainAFDeriv` on `d` to `(v1.1, v1.2 - readN(y₀) • v1.1)` so the `packLayer1` equals `chainUnitMap (readN⟨0⟩ y₀) v1`.

**Q3 – Base-point consistency**
- `chainUnitMap (readN ⟨0⟩)` uses `readN ⟨0⟩ (pbo u)` as its fixed matrix, by definition of `pbo`. In the derivative formula, the same base value appears inside `chainAFDeriv`, because `hasFDerivAt_chainA` evaluates the pointwise `Nf y₀`. Ensure you normalize the name:
  ```
  have hN0 : readN ⟨0⟩ y₀ = _
  ```
  so both sides use the identical matrix. No hidden term appears because `dN d = 0`, and `chainAFDeriv` has precisely `- N(y₀)·dW d`. There is no term involving `dN·W` since it annihilates with `dN d = 0`.

**Practical Lean tips**
- Keep lemmas small: first prove the equality of the functions, then the `HasFDerivAt`, then the `fderiv` equality, each as separate statements to avoid `simp` blow-ups.
- When massaging indices, prefer `by_cases h : i < schurT1` followed by `cases (finSplit _).symm ...` to align the `Fin` permutations; automation with `simp` using `Fin.cast` often succeeds once hypotheses like `by decide` are available.
- Once the final equality is in place, finish J11 with a short `simp` block replacing the CLM evaluations by the values from Q2, and use the reduction lemma to `chainUnitMap`.

Let me know if you want the supporting lemmas sketched explicitly or help wiring the final `simp` proof.
