Verdict: the injectivity argument is sound under the stated `DivBirthInv` hypothesis. I found no gap or circularity.

1. Birth validity

FACT: `widthMinUpto M n` is the infimum over every `i : Fin (L+1)` with `i.val ≤ n`, and `widthMinUpto_le` has exactly that hypothesis.

For `n = layer + 1`:

- Row index has value `layer`, and `layer ≤ layer + 1`.
- Column index has value `layer + 1`, and `layer + 1 ≤ layer + 1`.

Thus
`cleared < widthMinUpto M (layer+1) ≤ M i`
for both indices. The inequality direction is correct: being below the minimum is stronger than being below either width.

2. Fallback branches

FACT: `birthFlatCoord_of_valid` proves separately for every divisor that all three guards succeed, then rewrites `birthFlatCoord` to its real `equivFin` branch.

`birthFlatCoord_injective` applies this lemma to both `k` and `k'` before using their coordinate equality. Consequently, neither side can be a fallback value under `DivBirthInv`.

INFERENCE: the total function can collide off-cone. For example, two distinct invalid corners failing `a < L` both map to `⟨0,h⟩`. This does not affect the theorem because `DivBirthInv` supplies validity for every divisor.

When `flatDim M = 0`, `leafOfState` instead has an empty divisor index type, so injectivity is vacuous; it does not invoke the fallback.

3. `flatIdx_corner_inj`

FACT: equality of the outer sigma yields:

- equality of the inner row indices, hence equality of their `Fin L` layer components;
- an `HEq` between the column components.

Once the layers agree, the column types agree because the column width depends only on `layer.succ`, not on the row coordinate. `Fin.heq_ext_iff` then reduces the column `HEq` to equality of their natural values, giving `b = b'`.

Discarding the row `HEq` is therefore safe. No distinct `(a,b)` and `(a',b')` can encode the same diagonal `FlatIdx`.

4. Freshness induction

FACT: all transitions close the invariant:

- Root: all clauses are vacuous.
- Merge: relevant fields are definitionally unchanged.
- Birth: old freshness excludes `(layer,cleared)` from the old range; old corners remain fresh after `cleared + 1`, and the new corner satisfies `cleared < cleared + 1`.
- Rollover: every old corner has birth layer `≤ old layer`, so none has layer `old layer + 1`; freshness at the new layer is vacuous.

In particular, immediately after rollover, a birth at `(newLayer,0)` cannot collide with an old corner.

5. Circularity

FACT: the dependency is one-way:

`root → transition maintenance of DivBirthInv → injective divBirthCoord → injective birthFlatCoord → injective filtered leaf map`.

Birth maintenance uses the previous state’s freshness and `divBirthCoord` injectivity. It never uses `birthFlatCoord_injective`. Conversely, `birthFlatCoord_injective` explicitly uses the already-established `divBirthCoord` injectivity.

The theorem does assume corner injectivity as part of `DivBirthInv`; it does not derive it from validity alone. But that assumption is independently established from the root and preserved through every construction child, so this is induction, not circularity.