**1. RECOMMENDED FACTORING (Q1)**

Use an explicit shared last split, concretely `J : Fin r ↪ Fin (H (Fin.last L))` with

```lean
eLast := pivotThresholdSplit r (H (Fin.last L)) J
```

and thread the same `J` into both `deepestEPivot` and `framedParams_split_eq_frame_raw`.

Inference: the cleanest internal factoring is probably a split-parametrized core, e.g. “with last codomain split `eLast`”, with the pivot version specialized by `J`. But do not keep `deepestEPivot` threshold-based and post-compose only the `P12` block. That does not minimize PIN2 coupling: changing the final column split mixes old `P11` and `P12` columns, and the residual has a built-in `P11 - I` constant, so this is not a harmless permutation of `P12`.

Minimal PIN2 touch: make PIN2 read the same last-column split as `deepestEPivot`; otherwise the `rw [h00,h01,h10]` alignment problem remains.

**2. deepestEPivot_base SOUNDNESS (Q2)**

Definitive answer from the stated facts: if the zero product remains the `rThresholdSplit` corner and only the final read is changed to `pivotThresholdSplit J`, then `deepestEPivot_base` is FALSE for arbitrary non-front `J`.

Reason: the threshold-corner matrix is supported on the first `r` threshold columns. Re-reading its columns by an arbitrary pivot split gives a block matrix that equals `[I 0; 0 0]` only when the pivot set is exactly the first `r` columns, with the compatible order. Otherwise some identity columns move into the new `P12` block and/or disappear from the new `P11` block. So `P11 - I` and `P12` need not vanish.

So there is a real soundness trap. Base becomes true again only under the full L1 convention: the last-layer `.succ`-side base corner is also built/read using `eLast = pivotThresholdSplit J`, so the zero product is a pivot corner, not merely a threshold corner re-read by pivots.

**3. SUB-STAGING (Q3)**

1. GREEN-BANKABLE: prove pure matrix/reindex block identities for arbitrary splits, especially the discriminating identity with matching inner and outer `eJ`.

2. GREEN-BANKABLE: add a split-parametrized or pivot-specialized auxiliary residual map under a new name, leaving old `deepestEPivot` and PIN2 untouched.

3. GREEN-BANKABLE, conditional: prove the value-fold identity and strict derivative wrapper for that new pivot/split-parametrized map, assuming `hQf22 : IsUnit ((reindex eLast eLast Qf_last).toBlocks₂₂)`. This is additive only if it does not replace the old definitions.

4. RED-SPAN: rename/swap the production `deepestEPivot` to use `J/eLast`.

5. RED-SPAN: migrate `deepestEPivot_base`, `deepestEPivot_sq_sum_eq_blocks`, PIN2 `framedParams_split_eq_frame_raw`, and the `deepest_loss_squeeze` call chain to the same `J`.

Largest green-bankable prefix: through the pivot auxiliary derivative theorem, provided the pivot map and L1 last-slice formulas are introduced additively.

**4. L1-vs-L2 + WHICH REINDEX (Q4)**

Your L1 read is correct.

For the certified `B22` to appear, both must use the same `eJ := pivotThresholdSplit ... J`:

```lean
reindex eR eJ
  ((reindex eR.symm eJ.symm (fromBlocks 0 Y 0 0)) * Q)
```

Then the `P12` block is

```lean
Y * (reindex eJ eJ Q).toBlocks₂₂
```

So yes: the `.succ`-side reindex in the last-layer regular-slice lemma must migrate from `rThresholdSplit` to `pivotThresholdSplit J`, at least for the last layer’s column side. The row side stays threshold.

If only the outer final read changes, while the last-layer perturbation is still inserted with threshold `.succ` split, the term becomes the mixed block

```lean
Y * (reindex eThreshold eJ Q).toBlocks₂₂
```

not the Stage-A-certified

```lean
Y * (reindex eJ eJ Q).toBlocks₂₂
```

**5. SINGLE CHEAPEST DISCRIMINATING CHECK**

Before the coupled migration, prove/check this isolated matrix identity:

```lean
(reindex eR eJ
  ((reindex eR.symm eJ.symm (fromBlocks 0 Y 0 0)) * Q)).toBlocks₁₂
=
Y * (reindex eJ eJ Q).toBlocks₂₂
```

Also check the threshold-inner variant gives the mixed `reindex eThreshold eJ Q` block. That single contrast confirms whether the migration is L1-sound or accidentally L2-unsound.