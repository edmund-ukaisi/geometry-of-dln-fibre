**1. Split**

Use the **flat coordinate route**, not full `paramsEquivFlat` composition. The source is already `Fin (flatDim H) → ℝ`; `paramsEquivFlat` should only appear in `flatDeepest` and in the pulled-back loss.

Do **not** make `split` be “matmul by arbitrary `P,Q` units” unless you also prove the determinant product has absolute value `1`. Mathlib has the scaling theorem `Real.map_linearMap_volume_pi_eq_smul_volume_pi`, so arbitrary linear maps rescale volume by `|det|⁻¹`; they are not automatically MP. `volume_preserving_arrowCongr'` only covers coordinate relabeling.

Clean route:

- define a structured index
  `SplitIdx := RegIdx ⊕ (CoreIdx ⊕ GaugeIdx)`;
- set `CoreIdx := FlatIdx (deepestM H r)` and `nGauge := Fintype.card GaugeIdx`;
- build one equivalence
  `FlatIdx H ≃ SplitIdx`;
- flatten to `Fin (flatDim H)` / `Fin (flatDim M)` only at the boundary via `Fintype.equivFin`;
- define `split` as:
  translation by `-flatDeepest`, then coordinate reindex, then unpack `(⊕)` into products.

Mathlib/repo has: `volume_preserving_arrowCongr'`, `volume_measurePreserving_piCongrLeft`, `Homeomorph.sumArrowHomeomorphProdArrow`, `measurePreserving_piCurry` in the repo, and translation MP via `measurePreserving_add_right`.

Needs building: likely a small MP lemma for `sumArrowHomeomorphProdArrow` if not already local.

Biggest split risk: **the finite-index equivalence**, not measure. Avoid proving
`nReg + flatDim M + nGauge = flatDim H` by arithmetic everywhere; encode the partition as an actual equivalence of finite index types.

**2. CoreAbsorb**

For the current target, `coreAbsorb` should be the **full map whose core output is the `Rcore` used by `loss_squeeze`**. Do not make the structure field only the MP Schur shear `(a)` unless you change the target: then `Φ` contains `∏S_s`, while the banked squeeze wants the full-product Schur `R`.

Best factoring:

```text
coreAbsorb = b ∘ a
a = per-layer additive Schur shear, det 1, MP
b = inter-layer unit absorption, non-MP bounded-unit Jacobian
```

Prove fields for the composite, but prove `coreAbsorb_rlct` by factoring internally:
first `rlctAtOn_comp_homeomorph` for `a`, then weighted transport + unit-weight peel for `b`.

Biggest coreAbsorb risk: the target asks for a **global** `≃ₜ`. If the formula uses `(1+X)⁻¹` only near `0`, you need a continuous totalized coefficient equal to the true inverse on the neighborhood used by the squeeze. Otherwise you will get stuck trying to make a local Schur chart into a global homeomorphism.

**3. CoreAbsorb_RLCT**

For `b`, set `F q := ∑ i, q.1 i^2 + coreF q.2.1`.

Use:

```text
weightedThreshold_transport F 1 0 b Db ∅ ...
weightedThreshold_weight_unit_invariant (F ∘ b) (fun q => |(Db q).det|) 0 ...
```

With `E = ∅`, the transport hypotheses are mostly cheap if `b` is a homeomorphism:
`Homeomorph.isProperMap`, surjectivity/injectivity from `b`, image-null by simp.

You must show near `0`:

```text
a ≤ |(Db q).det| ∧ |(Db q).det| ≤ b
```

with `0 < a`. The cleanest proof is usually:

- prove determinant formula;
- show determinant is continuous;
- show determinant at `0` is `1`;
- take bounds like `1/2 ≤ |det| ≤ 3/2` on a small neighborhood.

The determinant should be a product of powers of inter-layer unit determinants, of the form

```text
∏ s, |det G_s(q)| ^ k_s
```

where `G_s` is something like `I - V_s Y_s` or its inverse, depending on direction. Do not over-optimize the closed form; for the weight peel, only continuity and nonzero value at `0` matter. Mathlib has `Matrix.det_fromBlocks_zero₁₂`, `Matrix.det_fromBlocks_zero₂₁`, `Matrix.det_blockDiagonal`, and `Matrix.det_of_blockTriangular`; the Jacobian block-triangular packaging likely needs building.

**4. Loss_Squeeze**

Wire this last and do it in split coordinates. Let `V ∈ 𝓝 0` be the small neighborhood where the Schur identities, inverse bounds, and leak estimate hold, then set `U := split ⁻¹' V`; use `split_basepoint` to get `U ∈ 𝓝 flatDeepest`.

Use the banked chain:

```text
frobenius_fromBlocks
schur_P11_decomp
core_comparability_squeeze
```

For `hleak`, the Lean-friendly route is finite-dimensional boundedness, not abstract operator theory unless you already have Frobenius norm lemmas:

```text
leak = E10 * (I+E00)⁻¹ * E01
```

Show entries of `(I+E00)⁻¹` are bounded near `0`, then prove a finite-sum estimate

```text
∑ leak² ≤ C * (∑ E10²) * (∑ E01²)
```

and shrink the neighborhood so this is `≤ t² * ∑ E²`.

This is probably the hardest part of `loss_squeeze`, but not the whole construction. The harder global wall is still the full `coreAbsorb` homeomorphism plus its Jacobian.

**5. Order**

Build in this order:

1. `SplitIdx`/`GaugeIdx` and `split`, with MP and `split_basepoint`.
2. `coreAbsorb = b ∘ a`, with fixing fields and basepoint.
3. `coreAbsorb_rlct`, using MP shear then non-MP unit peel.
4. `loss_squeeze`, after all coordinate identities are stable.

Pair early on **coreAbsorb as a global homeomorphism plus Jacobian determinant**. If that design is wrong, both `coreAbsorb_rlct` and `loss_squeeze` will be forced into the wrong shape.