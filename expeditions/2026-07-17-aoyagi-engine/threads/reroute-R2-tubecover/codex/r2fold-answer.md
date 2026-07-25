## 1. VERDICT

Yes. The design is sound, the inclusion is correct, and no injectivity of `g i` is needed. The proposed definitions and theorem proof typecheck on the pinned v4.29 environment.

## 2. MEASURE PITFALLS

No measurability assumptions are needed: these lemmas operate on outer measure.

Verified v4.29 proof shape:

```lean
measure_mono_null hIncl <|
  measure_union_null hnode <|
    measure_iUnion_null fun i =>
      htransport i _ (ih i _ (hchild i))
```

Exact verified lemmas:

- `measure_mono_null`
- `measure_union_null`
- `measure_iUnion_null`
- `Set.mem_iUnion`

`Fin k` supplies `Countable`, including `k = 0`. Avoid rewriting measure of a difference via subtraction; your inclusion-plus-null-union route avoids measurability/finiteness bookkeeping entirely.

## 3. NULL-TRANSPORT

Yes: the abstract fold should assume precisely forward null transport.

For the real charts, the cleanest route is not measure preservation but differentiability:

```lean
exact
  addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    volume hg.differentiableOn hN
```

This exact statement is verified at v4.29. Import:

```lean
Mathlib.MeasureTheory.Function.Jacobian
```

It requires only differentiability on the null set, in the same finite-dimensional real space. It requires neither measurability of `N`, injectivity, global Lipschitzness, determinant one, nor an explicit σ-finiteness hypothesis.

Important trap: `MeasurePreserving.preimage_null` transports nullity backward, not forward. Forward transport from measure preservation needs inverse/equivalence data. Differentiability is much shorter. If `g` is the FanTree composite `blockBlowupMap ∘ shear`, prove the composite differentiable.

## 4. DESIGN

For the abstract layer, prefer a neutral new `ImageTree`, rather than extending the block-blowup-specific `FanTree`. Do not maintain it as a second concrete resolution tree: interpret the real tree into it, or apply the generic node lemma directly during the real-tree induction.

- `Fin k` is the leanest stored arity and works well.
- Use a Finset subtype `S` if named pivots/generators matter: `g : S → X → X`, `child : S → Tree`.
- Arbitrary stored `[Fintype ι]` adds dependent/universe bureaucracy with little benefit.
- Keep the leaf clause up-to-null. It is the weakest compositionally closed statement; full leaf cover can discharge it immediately.

Rename `NullTree` to `ImageTree`: nullity belongs to the predicate, not the tree data.

## 5. SCOPE

The tree theorem is a reasonable first rung, but the smallest reusable brick is the one-node gluing lemma:

```lean
μ (A \ ⋃ i, g i '' B i) = 0
→ (∀ i, μ (g i '' (B i \ C i)) = 0)
→ μ (A \ ⋃ i, g i '' C i) = 0
```

Prove this generic lemma first, then derive the transport-based wrapper and tree fold. That isolates all genuine set/measure bookkeeping; the structural induction becomes routine.