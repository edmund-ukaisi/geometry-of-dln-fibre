**Verdict: sound.** The reduction is a short bounded lemma; no non-square smeared chart-builder is needed for the L=2 spine under `1 ≤ minAdm ∧ BoundarySmeared`.

Proof, for the **actual chosen** `r = tStar`:

1. `1 ≤ minAdm ⟹ M2 ≥ 1` is valid.

   If `M2 = 0`, take `T0 = min(M0,M1)`. Then
   ```text
   Mval(T0) = (M0 - T0)(M1 - T0) + T0*M2 = 0
   ```
   because one factor is zero and `M2=0`. Hence the minimum value is `0`, contradicting `1 ≤ minAdm`.

2. From `BoundarySmeared`, using the given Lean classification:
   ```text
   BoundarySmeared ⟹ ¬InteriorDrop ∧ r < M1
   InteriorDrop ⟺ M2 > 0 ∧ r < M0 ∧ r < M1
   ```
   Therefore
   ```text
   ¬(M2 > 0 ∧ r < M0 ∧ r < M1)
   ```
   and since `r < M1` and `M2 ≥ 1`, i.e. `M2 > 0`, we get `¬ r < M0`, hence `r ≥ M0`.

3. Since `r` is an admissible minimizer, `r ≤ min(M0,M1)`, hence `r ≤ M0`.

   Therefore `r ≥ M0` and `r ≤ M0`, so `r = M0`.

**Nonuniqueness subtlety:** no gap. The branch predicate and `deepRank` both use the same chosen `r = tStar`. If `Classical.choose` picked some other minimizer `r < M0`, then with `1 ≤ minAdm` we still have `M2 > 0`; together with `r < M1`, that would force `InteriorDrop`, contradicting `BoundarySmeared`. So the reduction holds for the actually chosen minimizer, not merely for some preferred minimizer.

So the Lean spine can use:

```text
1 ≤ minAdm → BoundarySmeared → r = M0
```

and dispatch smeared entirely to the already-built square case.