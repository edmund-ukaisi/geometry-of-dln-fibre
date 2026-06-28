**Certainty:** The chain is right. `schur_frame_transform` is only needed if your `rcore_schur_factor_of_corner_split` is stated for an unframed core but `Score` is framed. As described, `rcore_schur_factor...` already matches Score’s `+1` Schur integrand, so it is redundant here.

A cast-stable tail should go by **matrix equality**, then `congrArg frobSq`:

```lean
  -- after `rw [hstepA]`
  have hLDU :
      scoreSchurExpr x = Shat0 * (1 - Khat) * Shat1 := by
    simpa only [Mw, Mhat, G0, G1, scoreSchurExpr]
      using rcore_schur_factor_of_corner_split
        Mw Mhat eR eMid eC G0 G1 hGG hsplit

  have hRead :
      Shat0 * (1 - Khat) * Shat1 = prod (deepestM H r) c := by
    -- threaded readback tie, plus the L=2 product peel
    rw [prod_deepestM_eq_two_of_L2]
    simp only [hclast, hc0, lastLayer, Fin.isValue]
    simpa only [finCongr_refl, reindex_refl_refl, Matrix.mul_assoc]
      using hReadbackTie

  have hScore :
      Score x = frobSq scoreSchurExpr x := by
    rw [hScoreDef]
    rfl   -- or: simp [frobSq]

  rw [hScore]
  exact (congrArg frobSq (hLDU.trans hRead)).symm
```

If `hScoreDef` unfolds directly to the double sum rather than `frobSq`, replace the `rfl` line with:

```lean
    simp [frobSq]
```

Q2: yes, treat `frobSq` as an ordinary function. Do **not** rewrite under the sums. Prove matrix equality

```lean
hMat : scoreSchurExpr x = prod (deepestM H r) c
```

then close with:

```lean
exact (congrArg frobSq hMat).symm
```

Q3: the clean contract is to thread the three pivots as typeclass instances if the lemma requires `[Inv ...]` / `[Invertible ...]`. Produce them outside this tail from determinant facts via `invertibleOfNonzeroDet` or your local equivalent. Do not build them inline inside the assembly unless necessary; instance synthesis here is fragile.

Q4: make the alignment lemma explicit. The risky part is not `frobSq`; it is the equality

```lean
prod (deepestM H r) c = G0 * G1
```

after `prod_deepestM_eq_two_of_L2`. Use a banked/readback lemma whose RHS already uses the same `G0 G1 eR eMid eC` as `rcore_schur_factor`. Then normalize only identities:

```lean
simp only [finCongr_refl, reindex_refl_refl]
erw [Matrix.mul_assoc]
```

**Missing if not already banked:** `hReadbackTie` as a single matrix equality in the same frames/casts. Without that, STEP 3-4 is not just assembly.