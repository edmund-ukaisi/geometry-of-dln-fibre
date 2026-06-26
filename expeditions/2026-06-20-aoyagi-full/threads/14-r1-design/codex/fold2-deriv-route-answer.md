**Ranking**

1. **B**. Set `D_E := fderiv ℝ deepestEPivot 0`; prove only the reg-slice derivative is `id`; package invertibility by `clmShearEquiv`.  
   Biggest risk: the reg-slice coordinate simp may hit the `regGaugeIdxSplit`/`regResidualPack` packing wall.

2. **A**. Most canonical mathematically, but high Lean cost.  
   Biggest risk: dependent `prodAux` casts plus named Leibniz derivative will spread through every entry.

3. **D = factor out the shear lemma first**: prove a generic `regStraightenTotalCLM_equiv_of_regBlock_id`, then feed it any `D_E` with reg-block `id`. This is useful, but still needs B or A for `hblock`.

4. **C**. Avoid.  
   Biggest risk: direct `littleO` for the whole product is just unnamed Leibniz with worse API support.

**Top Route: B**

Use:

```lean
let E := deepestEPivot H r hr hL
let D_E := fderiv ℝ E (0 : Reg × Gauge)

have hE : HasStrictFDerivAt E D_E 0 :=
  (deepestEPivot_contdiff H r hr hL).hasStrictFDerivAt (by simp)
```

Mathlib names I’m confident exist in v4.29:

- `ContDiff.hasStrictFDerivAt`
- `HasStrictFDerivAt.comp`
- `ContinuousLinearMap.hasStrictFDerivAt`
- `HasStrictFDerivAt.hasFDerivAt`
- `HasFDerivAt.fderiv`
- `hasStrictFDerivAt_pi''`
- `ContinuousLinearMap.id`, `.fst`, `.snd`, `.prod`, `.comp`

State these sublemmas:

```lean
def regInCLM : Reg →L[ℝ] Reg × Gauge :=
  (ContinuousLinearMap.id ℝ Reg).prod 0
```

```lean
lemma deepestEPivot_regSlice_hasStrictFDerivAt_id :
  HasStrictFDerivAt
    (fun r0 : Reg => deepestEPivot H r hr hL (r0, 0))
    (ContinuousLinearMap.id ℝ Reg) 0
```

Prove this coordinatewise by `hasStrictFDerivAt_pi''`. For each packed coordinate, unfold `deepestEPivot`, `framedParamsReg`, `framedLayer`, then use the gauge-zero slice facts for reads:

```lean
readX H r hr hL (r0, 0) s = if s = first then X_from_reg r0 else 0
readY H r hr hL (r0, 0) s = if s = last  then Y_from_reg r0 else 0
readZ H r hr hL (r0, 0) s = if s = first then Z_from_reg r0 else 0
```

Then the idempotent fold collapses because all non-pivot layers are

```lean
Matrix.fromBlocks 1 0 0 0
```

and the only first-order surviving sandwiches are:

```lean
corner * δC_s * corner
```

with block results:

```lean
toBlocks₁₁ : Σ_s X_s  -- gauge-zero slice: only pivot X, so this is X_reg
toBlocks₁₂ : Y_last
toBlocks₂₁ : Z_first
```

The simp/idempotency step should be a reusable lemma, not inline:

```lean
lemma regSlice_linear_part :
  HasStrictFDerivAt
    (fun r0 : Reg =>
      -- packed residual of prod H (framedParamsReg (r0,0))
    )
    (ContinuousLinearMap.id ℝ Reg) 0
```

Then derive the block identity:

```lean
lemma fderiv_deepestEPivot_regBlock :
  D_E.comp regInCLM = ContinuousLinearMap.id ℝ Reg := by
  have hcomp := hE.comp regInCLM.hasStrictFDerivAt
  have hid := deepestEPivot_regSlice_hasStrictFDerivAt_id H r hr hL
  exact (hcomp.hasFDerivAt.fderiv).symm.trans hid.hasFDerivAt.fderiv
```

Finally package invertibility generically:

```lean
lemma regStraightenTotalCLM_equiv_of_regBlock_id
    (D_E : Reg × Gauge →L[ℝ] Reg)
    (hblock : D_E.comp regInCLM = ContinuousLinearMap.id ℝ Reg) :
  ∃ e : DeepestSplit ≃L[ℝ] DeepestSplit,
    (e : DeepestSplit →L[ℝ] DeepestSplit) = regStraightenTotalCLM D_E
```

Define `N := regStraightenTotalCLM D_E - ContinuousLinearMap.id ℝ DeepestSplit`; prove `N.comp N = 0` by `ext q; simp [N, regStraightenTotalCLM, hblock_apply]`; then use `clmShearEquiv N hN`.

**Likely Wall**

The wall is `deepestEPivot_regSlice_hasStrictFDerivAt_id`, specifically making `regResidualPack` and `regGaugeIdxSplit` expose that the regular coordinates are exactly `(X_first, Y_last, Z_first)`. Fallback: do A only for the reg-slice, not full `(reg,gauge)`: name a restricted Leibniz derivative for `fun r => prod H (framedParamsReg (r,0))`; collapse it to `id`; still keep `D_E := fderiv` for the full map.