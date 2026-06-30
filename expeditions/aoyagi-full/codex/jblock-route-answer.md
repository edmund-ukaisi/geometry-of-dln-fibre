**Q1 – J00/J01 assembly**  
- The route you sketch works verbatim once you phrase it as a composition of `HasFDerivAt`. Start from  
  ```lean
  have hfun :
      (fun z => BparamsLeaf ha z 0)
        = (fun z => (reindexLE ha).symm (layer0SchurMap ha hr hc z)) := by
    funext z; ext i j; simpa [Function.comp, BparamsLeaf_layer0_entry]
  ```  
  (replace `(reindexLE ha).symm` with the actual equivalence name used in your file; the point is to rewrite at function level before differentiating.)  
- Apply the chain rule with the linear equivalence:  
  ```lean
  have hdiff :
      HasFDerivAt (fun z => BparamsLeaf ha z 0)
        (((reindexLE ha).symm.toContinuousLinearEquiv : _ ⊸ _).toContinuousLinearMap.comp
          (layer0SchurMap_hasFDerivAt ha hr hc).fderiv) y₀ :=
    (ContinuousLinearEquiv.comp_hasFDerivAt _ (layer0SchurMap_hasFDerivAt ha hr hc)).congr hfun
  ```  
  (`ContinuousLinearEquiv.comp_hasFDerivAt` is `LinearIsometryEquiv.comp_hasFDerivAt`/`ContinuousLinearMap.hasFDerivAt`. Use whichever name matches your imports; in 4.29 it’s `ContinuousLinearEquiv.comp_hasFDerivAt`.) Extract the derivative with `have := hdiff.fderiv`.  
- Packing: `packLayer0` is literally `(flatBlockLE hr hc).symm` composed with the reindex equivalence, so  
  ```lean
  have := congrArg ContinuousLinearMap.toLinearMap hdiff.fderiv
  -- clean up coercions with `simp [packLayer0, LinearIsometryEquiv.comp_toContinuousLinearEquiv] at this`
  -- conclude `packLayer0 ... = (flatBlockLE hr hc).symm (fderiv _ ...)`.
  ```  
  Use `simp [packLayer0, ContinuousLinearEquiv.coe_coe, LinearMap.comp_apply]` to kill the reindex factors.
- Collapse `flatBlockLE` with the banked identity  
  ```lean
  have hcore :
      (flatBlockLE hr hc).symm.toContinuousLinearMap.comp
        (layer0SchurMap_hasFDerivAt ha hr hc).fderiv
          = (schurFrameDeriv _ _ _).toContinuousLinearMap.comp
            (slotReadV0_hasFDerivAt ha y₀).fderiv := by
    simpa [gate_schurCore_eq] using layer0SchurMap_hasFDerivAt_fderiv ha hr hc
  ```  
  (`layer0SchurMap_hasFDerivAt_fderiv` is the direct translation of your banked statement; if you stored it only as `HasFDerivAt`, do the same `congrArg`.)
- For the direction evaluation, use the generic linear lemma: in mathlib `fderiv_of_linear`/`HasFDerivAt.linear`. Since `slotReadV0` is linear,  
  ```lean
  have hslot :
      fderiv ℝ (fun y => slotReadV0 ha y) y₀ = (slotReadV0 ha).toContinuousLinearMap := by
    simpa using (slotReadV0_hasFDerivAt ha y₀).hasFDerivAt_fderiv
  ```  
  Then evaluate at `d := (eIn ha).symm (v0, (0, ()))` via  
  ```lean
  have hdir : slotReadV0 ha ((eIn ha).symm (v0, (0, ()))) = v0 := by
    simpa using slotReadV0_eIn_symm ha v0
  ```  
  so  
  ```lean
  have J00 :=
    by
      simpa [hdir] using
        ContinuousLinearMap.congrArg_apply
          ((schurFrameDeriv _ _ _).toContinuousLinearMap) hdir
  ```
  After `simp` everything collapses to `schurFrameDeriv _ _ _ v0`.  
- J01 is identical except the input direction has zero V0 component. Invoke the same lemma with `simp [hslot]` to get zero and finish with `map_zero`.

**Q2 – Idiom choice**  
- Option (b) is cleaner: prove `HasFDerivAt` via `ContinuousLinearEquiv.comp_hasFDerivAt` and only use the pointwise equality once at the function level. This avoids extra `Fin` rewrites inside `fderiv_comp`. Tactical skeleton:
  ```lean
  have hfun := ...
  have hbase := layer0SchurMap_hasFDerivAt ha hr hc
  have hcomp :
      HasFDerivAt ((reindexLE ha).symm ∘ layer0SchurMap ha hr hc)
        (((reindexLE ha).symm.toContinuousLinearEquiv).toContinuousLinearMap.comp hbase.fderiv) y₀ :=
    ((reindexLE ha).symm.toContinuousLinearEquiv.comp_hasFDerivAt hbase).congr hfun
  exact hcomp.fderiv
  ```  
  You then plug this `fderiv` straight into `packLayer0`. No nested `fderiv_comp` nor `fun_like.ext`. With (a) you still end up invoking (b) internally, so (b) wins on minimising `Fin.cast` churn.

**Q3 – J11 route**  
- Produce the function equality once:  
  ```lean
  have hfun1 :
    (fun z => BparamsLeaf ha z 1)
      = (fun z => (reindex₁ ha).symm (Agen 1 M (tach M) (genBlkFlatLive ...) hle 1 z)) := ...
  ```  
  Then rewrite `Agen 1 ... 1` with the chain decomposition:  
  ```lean
  have hAgen :
    Agen 1 ... 1 z = chainA (readN ⟨0⟩) (readW ⟨0⟩) (readC ⟨1⟩) z := ...
  ```  
  (`chainA` naming depends on your file; use the stored lemma coming from the bank.) Combine the two for an explicit `chainA` after reindexing.  
- Differentiate using the banked `hasFDerivAt_chainA` (or `chainAFDeriv`):  
  ```lean
  have hchain := hasFDerivAt_chainA ... z y₀
  have hdiff :=
    ((reindex₁ ha).symm.toContinuousLinearEquiv.comp_hasFDerivAt hchain).congr hfun1
  let L := hdiff.fderiv
  ```  
- Now interpret `packLayer1` as the composite of the `rowSplitLE` isometry and the final swap (`prodComm`):  
  ```lean
  have hpack :
      packLayer1 ha =
        ((prodCommLinearEquiv _ _).toContinuousLinearEquiv).toContinuousLinearMap.comp
        ((rowSplitLE ha).toContinuousLinearEquiv).toContinuousLinearMap ∘
        (reindex₂ ha).toContinuousLinearMap := rfl
  ```  
  Apply this to `L`. The banked lemma `chainAFDeriv` already states that the derivative of `chainA` is the block map `(ΔW, ΔC) ↦ (ΔW, ΔC - N ΔW)`. After pushing through the reindexing and the `rowSplit`/swap, you literally obtain the matrix pair.  
- Evaluate at the direction `d := (eIn ha).symm (0, (v1, ()))`. The `rowSplitLE` part will zero out the Schur block because the first component is `0`. What remains is the pair `(v1.1, v1.2 - N · v1.1)`, which matches `chainUnitMap (readN ⟨0⟩)`. The only nontrivial step is managing coercions; peel them with:
  ```lean
  have hslot1 :
      slotReadV0 ha ((eIn ha).symm (0, (v1, ()))) = 0 := ...
  have hslot2 :
      slotReadV1 ha ((eIn ha).symm (0, (v1, ()))) = v1 := ...
  ```  
  (You already banked the `V0` equation; the `V1` one is similar or already in the file.) Feed these into the `chainAFDeriv` expression, then `simp` the product swap/open to land exactly on `chainUnitMap (readN ⟨0⟩) v1`.  
- Tactical sketch for the last line:
  ```lean
  have hdir := congrArg _ hdiff.fderiv -- as before
  have hpackEval :
      packLayer1 ha (L ((eIn ha).symm (0, (v1, ())))) =
        chainUnitMap (readN ⟨0⟩) v1 := by
    simpa [packLayer1, chainUnitMap, hslot1, hslot2] using ...
  exact hpackEval
  ```

**Potential traps**  
- Ensure every equivalence (`reindexLE`, `rowSplitLE`, swaps) is used via its `toContinuousLinearEquiv` so `simp` sees coercions. `simp [ContinuousLinearEquiv.coe_coe, LinearMap.comp_apply]` is your friend.  
- When using `congr` with `HasFDerivAt`, reach for `HasFDerivAt.congr` or `ContinuousLinearEquiv.comp_hasFDerivAt` directly; avoid `funext` inside `HasFDerivAt` conclusions—they’re defeq but explode with `Fin.cast`.  
- `slotReadV0` linearity: rewrite using the lemma you cited (`slotReadV0_eIn_symm`). For Lean coherence, keep directions as `ContinuousLinearMap` applications (`L (eIn.symm _)`) and only project to V0/V1 after converting back to plain functions with `ContinuousLinearMap.coe_coe`.
