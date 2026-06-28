**Recommendation**

Define the chart in flat coordinates, not through `paramsEquivFlat ∘ smParams`:

```lean
noncomputable def smPivotCoord ... : Fin (routeMAmbient M) :=
  flatCoordOf M ⟨⟨deepLayer M hL, ⟨0, hrow⟩⟩, ⟨0, hcol⟩⟩

noncomputable def smearShiftFlat ... (u : Fin (routeMAmbient M) → ℝ) : ℝ :=
  smearShift M hL u hm1 hcol

noncomputable def phiSm ... (u : Fin (routeMAmbient M) → ℝ) :
    Fin (routeMAmbient M) → ℝ :=
  Function.update u (smPivotCoord M hL hrow hcol)
    (u (smPivotCoord M hL hrow hcol) - smearShiftFlat M hL hm1 hcol u)
```

Do **not** make `smearShiftFlat` literally take `Fin n → ℝ` through `p*.succAbove`. Keep it as `smearShift ... u`, then prove the key invariant:

```lean
theorem smearShiftFlat_update_pivot
    (a : ℝ) :
    smearShiftFlat ... (Function.update u p* a) =
    smearShiftFlat ... u
```

This keeps the rate/Params connection direct. The `succAbove` factoring should be hidden inside one generic MP lemma.

**MP Route**

Add a width-free wrapper around the landed `measurePreserving_shearAt`:

```lean
theorem measurePreserving_updateSub_of_coordInvariant {N : ℕ}
    (p : Fin N) (f : (Fin N → ℝ) → ℝ)
    (hf : Measurable f)
    (hinv : ∀ u a, f (Function.update u p a) = f u) :
    MeasurePreserving
      (fun u => Function.update u p (u p - f u))
      (volume : Measure (Fin N → ℝ)) volume := by
  -- match N, p with | n+1, p => ...
  -- set g y := - f (Fin.insertNth p 0 y)
  -- call measurePreserving_shearAt p g
```

Inside that lemma, destructure `N` once. Then define:

```lean
g : (Fin n → ℝ) → ℝ := fun y => - f (Fin.insertNth p 0 y)
```

and prove

```lean
g (fun k => u (p.succAbove k)) = - f u
```

using `Fin.insertNth_apply_same`, `Fin.insertNth_apply_succAbove`, and `hinv`.

So the generic chart proof is just:

```lean
exact measurePreserving_updateSub_of_coordInvariant
  p* (smearShiftFlat M hL hm1 hcol)
  smearShiftFlat_measurable
  smearShiftFlat_update_pivot
```

No need to expose `routeMAmbient M = n+1` at the chart site.

Mathlib/local status: `measurePreserving_shearAt` is local and landed. A ready width-free version does not appear to exist locally. `fun_prop` for measurability through `Matrix.inv` should be verified; if it fails, prove measurability of `routing 0 r` by reducing the `Fin 1 × Fin 1` inverse to scalar division.

**Connection Lemma**

Prove:

```lean
theorem paramsEquivFlat_symm_phiSm_eq_smParams
    (hc1 : M (deepLayer M hL).succ = 1) :
    (paramsEquivFlat M).symm (phiSm M hL hrow hcol hm1 u)
      = smParams M hL u hrow hcol hm1 := by
```

Route:

1. Add `flatCoordOf_injective M`. Best proof is via a small `flatCoordEquiv : FlatIdx M ≃ Fin (routeMAmbient M)`, avoiding fragile `Fin.cast` rewriting.

2. `funext s i j`; set
   ```lean
   q : FlatIdx M := ⟨⟨s, i⟩, j⟩
   q* : FlatIdx M := ⟨⟨deepLayer M hL, ⟨0,hrow⟩⟩, ⟨0,hcol⟩⟩
   ```

3. Branch on `q = q*`, not on flat-coordinate equality.

4. Pivot branch: `paramsEquivFlat_symm_decode`, `phiSm`, `Function.update_self`, `smParams`, `smearedDeepLayer`, `Matrix.updateRow_apply`. This gives the pivot value
   `deepCol ... ⟨0,hrow⟩ - smearShift ...`.

5. Non-pivot branch: use injectivity to get
   ```lean
   flatCoordOf M q ≠ p*
   ```
   so the LHS decodes to the unchanged `u (flatCoordOf M q)`, then back to `baseParams M u s i j`.

6. RHS non-pivot needs a helper:
   ```lean
   theorem smParams_apply_ne_pivot
      (hc1 : M (deepLayer M hL).succ = 1)
      (hq : q ≠ q*) :
      smParams ... q.1.1 q.1.2 q.2 =
      baseParams M u q.1.1 q.1.2 q.2
   ```
   If `s ≠ deepLayer`, use `Function.update_of_ne`. If `s = deepLayer`, `hc1` makes every column equal `0`; since `q ≠ q*`, the row is not `0`, so `Matrix.updateRow` is unchanged.

That `hc1` is essential: without `M_L = 1`, `smParams` changes all row-0 deepest columns, while `phiSm` changes only one flat coordinate.

**Measurable Embedding**

MP does not by itself give `MeasurableEmbedding`. Cheapest route: package the same invariant shear as a `MeasurableEquiv`:

```lean
noncomputable def updateSubME_of_coordInvariant ... :
    (Fin N → ℝ) ≃ᵐ (Fin N → ℝ) where
  toFun := fun u => Function.update u p (u p - f u)
  invFun := fun v => Function.update v p (v p + f v)
  ...
```

The inverse proofs use `hinv`. Then:

```lean
theorem measurableEmbedding_phiSm :
    MeasurableEmbedding (phiSm M hL hrow hcol hm1) := by
  rw [phiSm_eq_updateSubME]
  exact (updateSubME_of_coordInvariant ...).measurableEmbedding
```

This is much cheaper than the validate-small `split121/coreShear` scaffolding.

**Biggest Risk**

The likely wall is proving `smearShiftFlat_update_pivot`, not the MP destructuring. You need to show both `frontMat` and the residual `deepCol` reads are unaffected by changing the pivot flat coordinate. Once those invariance lemmas are in place, MP and measurable embedding are routine.