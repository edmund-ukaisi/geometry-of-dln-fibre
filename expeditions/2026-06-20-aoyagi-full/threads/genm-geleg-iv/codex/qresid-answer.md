**Short Answer**

Define `qResidGen` on the **Schur-chart output coordinates**, not by applying `schurChartRawGen` again.

So:

```lean
Q := qChainGen C₀ py
```

not

```lean
Q := schurChartRawGen (chainOf py) L
```

Here `C₀` should be the already-packed base chart value, i.e. the general-L analogue of the L=2 `C₀ := schurChartRaw P₀`.

**1. Definition Shape**

Use a finite chart-output block point:

```lean
noncomputable def qBlockGen
    (C₀ : BlockParamsGen H r)
    (py : (Fin (nRegGen H r) → ℝ)
        × ((Fin (flatDim (fun s => H s - r)) → ℝ)
        × (Fin (specDimGen ι hι hL) → ℝ))) :
    BlockParamsGen H r :=
  blockFlatEquivGen H r ι hι ((splitHomeoGen ι hι hL).symm py) + C₀
```

Then bridge this `Fin L` block family to the `ℕ`-chain type used by `blockDiagProd`/`recoverProductGen`:

```lean
noncomputable def chainOfBlockParamsGen
    (B : BlockParamsGen H r) :
    (s : ℕ) →
      Matrix (Fin r ⊕ Fin (deepestChainWidth H s - r))
             (Fin r ⊕ Fin (deepestChainWidth H (s + 1) - r)) ℝ :=
fun s =>
  if hs : s < L then
    Matrix.reindex
      (Equiv.sumCongr (Equiv.refl (Fin r))
        (finCongr (by rw [deepestChainWidth_castSucc H s hs])))
      (Equiv.sumCongr (Equiv.refl (Fin r))
        (finCongr (by rw [deepestChainWidth_succ H s hs])))
      (B ⟨s, hs⟩)
  else
    Matrix.fromBlocks 1 0 0 0
```

The tail is not read by `blockDiagProd Q L`; `fromBlocks 1 0 0 0` is a good harmless tail if later prefix-pivot unit hypotheses appear.

Then:

```lean
noncomputable def qChainGen (C₀ : BlockParamsGen H r) (py : SplitGen ...) :=
  chainOfBlockParamsGen H r (qBlockGen ι hι hL C₀ py)
```

For the residual, write the formula directly with this `Q`:

```lean
noncomputable def qResidMatGenCore
    (C₀ : BlockParamsGen H r)
    (Br022 : Matrix (Fin (deepestChainWidth H 0 - r))
                    (Fin (deepestChainWidth H L - r)) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ)
    (py : SplitGen ...) :
    Matrix (Fin (deepestChainWidth H 0 - r))
           (Fin (deepestChainWidth H L - r)) ℝ :=
  let Q := qChainGen ι hι hL C₀ py
  let last := L - 1
  (Q 0).toBlocks₂₁ * G ((Q last).toBlocks₁₁) * (Q last).toBlocks₁₂
    + blockDiagProd Q L
    - Br022
```

In the public `qResidMatGen`, add endpoint `finCongr` casts so the result has type

```lean
Matrix (Fin (H 0 - r)) (Fin (H (Fin.last L) - r)) ℝ
```

If you can parameterize the theorem by `last : ℕ` with number of layers `last + 1`, do that. It avoids most `L - 1` / `last + 1 = L` casts.

**Do not use**:

```lean
Q := schurChartRawGen (qChainGen C₀ py) L
```

inside `qResidMatGen`. That double-applies the Schur chart. It also puts `redFactorGen` and its partial-product inverses into the residual, so `ContDiff ℝ 1` would no longer follow from only `ContDiff ℝ 1 G`.

**2. ContDiff Structure**

With the direct definition:

- entries of `qBlockGen` are `C^∞`: `blockFlatEquivGen` is a continuous linear equivalence, `splitHomeoGen.symm` is `C^∞`, and `+ C₀` is smooth;
- entries of `qChainGen` are still `C^∞`, just reindexed/cast entries of `qBlockGen`;
- `blockDiagProd Q k` is entrywise `C^∞` by induction on `k`;
- `G ((Q last).toBlocks₁₁)` is only `C¹`, by `hG.comp hM11`;
- the Schur term and final residual are `C¹`.

The induction for the diagonal product is:

```lean
theorem contDiff_blockDiagProd_entry
    (hQ : ∀ s i j, ContDiff ℝ (⊤ : ℕ∞) (fun py => Q py s i j)) :
    ∀ k i j, ContDiff ℝ (⊤ : ℕ∞)
      (fun py => blockDiagProd (Q py) k i j)
| 0, i, j => by
    simp [blockDiagProd]; exact contDiff_const
| k+1, i, j => by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun py => (blockDiagProd (Q py) k * (Q py k).toBlocks₂₂) i j)
    exact contDiff_matrix_mul_entry
      (fun a b => contDiff_blockDiagProd_entry hQ k a b)
      (fun a b => hQ k (Sum.inr a) (Sum.inr b))
      i j
```

`contDiff_matrix_mul_entry` exists in the L=2 file; reuse or move it.

**3. Slice Value**

Define the shift:

```lean
noncomputable def coreShiftParamGen
    (C₀ : BlockParamsGen H r) : Params (fun s => H s - r) :=
  fun s => (C₀ s).toBlocks₂₂
```

At `py = ((0), t)`, let

```lean
x := (splitHomeoGen ι hι hL).symm ((0 : Fin (nRegGen H r) → ℝ), t)
```

Use `bChart_slice_reg_zero_gen` to get:

```lean
(blockFlatEquivGen H r ι hι x (firstLayer hL)).toBlocks₂₁ = 0
(blockFlatEquivGen H r ι hι x (lastLayer hL)).toBlocks₁₁ = 0
(blockFlatEquivGen H r ι hι x (lastLayer hL)).toBlocks₁₂ = 0
```

Hence the three regular corners of `Q` equal the corresponding corners of `C₀`. With

```lean
hGeval : G (C₀ (lastLayer hL)).toBlocks₁₁ = ((C₀ (lastLayer hL)).toBlocks₁₁)⁻¹
h11 h12 h21
hschur : Br.toBlocks₂₂ = Br.toBlocks₂₁ * Br.toBlocks₁₁⁻¹ * Br.toBlocks₁₂
```

the Schur term cancels `Br.toBlocks₂₂` exactly as in L=2.

The remaining term is:

```lean
blockDiagProd Q L
```

and this becomes

```lean
prod (fun s => H s - r)
  (coreParamsGen ι hι x + coreShiftParamGen C₀)
```

by a new telescope lemma. I did not find an existing general lemma for this exact bridge; prove it.

Suggested new lemma name, verify no hidden duplicate:

```lean
-- new; verify no existing duplicate
theorem blockDiagProd_chainOfBlockParamsGen_eq_prod_toBlocks₂₂
    (B : BlockParamsGen H r) :
    endpointReindex
      (blockDiagProd (chainOfBlockParamsGen H r B) L)
      =
    prod (fun s => H s - r) (fun s => (B s).toBlocks₂₂)
```

Proof: induction on prefix length `k`. Base is `1 = prodAux ... 0`. Succ step unfolds both `blockDiagProd` and `prodAux_succ`, then uses the lemma saying the `₂₂` block of `chainOfBlockParamsGen B k` is the cast of `(B ⟨k, hk⟩).toBlocks₂₂`.

Then apply it to:

```lean
B := qBlockGen ι hι hL C₀ ((0), t)
```

and rewrite:

```lean
(B s).toBlocks₂₂
  =
coreParamsGen ι hι x s + coreShiftParamGen C₀ s
```

This part does not need regular-zero; it is just the definition of `coreParamsGen` plus pointwise addition.

**4. Biggest Trap**

The biggest trap is double-charting.

`qBlockGen C₀ py` should live in **chart-output coordinates**. If you set

```lean
Q := schurChartRawGen (qChainGen C₀ py) L
```

then `Q.toBlocks₂₂` is `redFactorGen`, not the core coordinate. You introduce partial-product inverses, lose global `ContDiff ℝ 1` from just `G`, and the slice product is no longer the direct reduced-core product.

Secondary trap: isolate the `Fin L ↔ ℕ` bridge and the `last = L - 1` casts. If possible, parameterize residual lemmas by `last` with `L = last + 1`; otherwise make one helper for `lastNat := L - 1` and one endpoint-reindex helper, then never do those casts inside the main algebra proof.