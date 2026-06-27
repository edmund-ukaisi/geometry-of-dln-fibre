**Recommendation: ARCH-1.**

Use the one collapse CLE

```lean
noncomputable abbrev bridgeCLE (M : Fin (L + 1) → ℕ) :
    (Fin (routeMAmbient M) → ℝ) ≃L[ℝ] Params M :=
  (paramsEquivFlatCLE M).symm
```

and make every factor

```lean
cleConjFactor (bridgeCLE M) g gD hg
```

with `g : Params M → Params M`.

ARCH-2 does not remove the alignment problem. It makes role reads direct, but then the final value in `RoleSpace` still has to be packed into the `paramsEquivFlat` / `FlatIdx` layout. That is the same permutation, only paid at the output boundary instead of the input boundary, and it puts the bridge target outside the natural home of `chartParamsGen`.

**Q1. Alignment**

Fact: with the current APIs, `paramsEquivFlat` and `chartIdxEquiv` are independent finite enumerations. So a hand-written semantic claim like “this role slot is layer `s`, row `i`, col `j`” will not be definitional unless you define that alignment yourself.

But for the bridge, the alignment is absorbable. Define Params-level role readers through the flat projection:

```lean
noncomputable def flatOfParams (M : Fin (L + 1) → ℕ) (P : Params M) :
    Fin (routeMAmbient M) → ℝ :=
  (paramsEquivFlatCLE M) P

noncomputable def readKParams (M t) (ha : StructAdm M t) (P : Params M) :=
  readK M t ha (flatOfParams M P)
```

Then

```lean
readKParams M t ha ((bridgeCLE M) x) = readK M t ha x
```

is just CLE cancellation, not an index proof. If you want semantic in-place block factors, add one explicit equivalence

```lean
chartFlatIdxEquiv : ChartIdx M (tDesc M t) ≃ FlatIdx M
```

mapping Schur slot `k` to the top rows of layer `k`, and lift slot `k` to the bottom rows of layer `k+1`. Prove that once at the equivalence level. Do not prove per-role/per-entry alignment lemmas.

**Q2. Determinants**

Yes: if you want to use `composeFold_eq_cleConj_foldr`, all factors in that list must use the same `bridgeCLE M`.

So `schurChartFactor E_s` / `lduChartFactor E_s` are the wrong outer packaging for this collapse. The underlying determinant facts are still exactly the right facts.

Use this pattern:

```lean
-- Params-level block split for one factor.
S : Params M ≃L[ℝ] SchurInc t r c × R

gSchur : Params M → Params M :=
  conjBlockMap S schurFrameMap

gSchurD : Params M → Params M →L[ℝ] Params M :=
  conjBlockDeriv S schurFrameD

schurFactorSameE : ChartFactor (routeMAmbient M) :=
  cleConjFactor (bridgeCLE M) gSchur gSchurD
    (conjBlock_hasFDerivAt S schurFrameMap schurFrameD
      (fun z => schurFrameMap_hasFDerivAt z))
```

Then the det proof is two rewrites:

```lean
rw [cleConjFactor_abs_det]
rw [conjBlock_abs_det]
-- leaves |det schurFrameD ((S ((bridgeCLE M) u)).1)|
-- then schurFrameD_abs_det
```

So no re-derivation of the Schur/LDU monomial determinant. The determinant is read as

```lean
(S ((bridgeCLE M) u)).1
```

not as `(bridgeCLE M u).1`, because `bridgeCLE M u : Params M`.

**Q3. Validation Case**

Use `(2,2,2)` first for brick (a). It is small but still tests the important bridge issues: `chartIdxEquiv`, role-slot reads, nontrivial Schur/lift allocation, and `chainA` row splitting.

It is too degenerate for the full determinant story: `1×1` blocks hide LDU ordering and most matrix-product structure. After the bridge works on `(2,2,2)`, validate a `2×2` K-core case. The existing `(3,3,3,3)` shape is better for LDU/Schur/chain stress than `(3,3,4)`, because it has the genuine `2×2` LDU core and multi-pivot spectator exponents. `(3,3,4)` is useful for the `N = 21` honest chart/pack story, but it is not the minimal LDU stress test.

**Q4. Concrete Brick-(a) Shape**

Use three layers of definitions.

```lean
noncomputable def genBlkParamsStruct
    (M t) (ha : StructAdm M t) (P : Params M) : GenBlk M t :=
  genBlkFlatStruct M t ha ((paramsEquivFlatCLE M) P)

noncomputable def phiParamsStruct
    (M t) (ha : StructAdm M t) (P : Params M) : Params M :=
  chartParamsGen
    (((paramsEquivFlatCLE M) P) ⟨0, by exact ...⟩)
    M t (genBlkParamsStruct M t ha P) (hleStruct M t ha)
```

For real factor ops, do not use `phiParamsStruct` as one giant map. Build the list in dependency order:

```lean
gs =
  chainOps   -- write A_s = chainA N_s W_s C_{s+1}
  ++ schurOps -- write C_{s+1} = [[K, KN], [XK, XKN + E]]
  ++ lduOps   -- write K = (1+L) diag(q) (1+U)
  ++ [radialOp] -- scale the active E/radial slots
```

Since `List.foldr (· ∘ ·) id` runs the rightmost map first, this makes `radialOp` run first.

The key bridge theorem should be:

```lean
theorem paramsOps_fold_eq_chartParamsGen
    (x : Fin (routeMAmbient M) → ℝ) :
    (gs M t ha).foldr (· ∘ ·) id ((bridgeCLE M) x)
      =
    chartParamsGen (x p) M t (genBlkFlatStruct M t ha x)
      (hleStruct M t ha)
```

The riskiest sublemma is not `readK`. It is the layer source/target split:

```lean
-- schematic
theorem chainLayer_slot_alignment (s : Fin L) :
  -- under chartFlatIdxEquiv, the source block
  --   C_{s+1} ⊕ W_s
  -- is exactly the top/bottom row split of Params layer s
```

Prove that at the equivalence level using `finSplit`, `schurSlotEquiv`, `liftSlotEquiv`, and the already banked `chainA_apply_castAdd` / `chainA_apply_natAdd`. Once that is in place, the final `funext s i j` proof is mechanical.