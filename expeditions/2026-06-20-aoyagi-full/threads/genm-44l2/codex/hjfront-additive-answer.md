Yes: **step 3 is sound**, and the route is **additive**, with one important caveat.

The column-dual peel works. Write the deepest last layer as `A_last`, its top `r` rows as `V`, and the prefix product as `G`. The native last-layer peel gives

```lean
B = G * A_last
```

and the banked deepest fact gives `A_last` tail rows vanish. Therefore the front `r` columns satisfy

```lean
B_front = (G.submatrix id (Fin.castLE ...)) * V_front
```

So if `B_front.rank = r`, then

```lean
r = rank B_front ≤ rank V_front ≤ r
```

hence `V_front.rank = r`, and the square front block is a unit. The `Classical.choice` in `deepestPoint` does **not** block this, because the proof uses only `prod deepestPoint = B` and the banked last-layer tail-row vanishing.

But: this **does not prove the existing** hypothesis

```lean
(deepestPoint_frame_pivot_exists ...).choose = frontEmbed
```

That chooser is arbitrary. If `V = [1 1]` with `r = 1`, both columns are valid pivots; front-full-rank does not force `Classical.choose` to select the front one. So the old `hJfront` is not dischargeable as stated.

The right route is exactly your `_front` variant: construct a front pivot frame with `J := frontEmbed` from the derived `V_front` unit, and rethread the L2 chain through that bundle. No edit to `deepestPoint_exists`, and no edit to `exists_pivot_cols_of_rank` is forced.

Cleaner implementation: factor the current pivot-frame proof into a deterministic helper

```lean
exists_pivotFrame_lastBlock_isUnit_of_pivot
  (J : Fin r ↪ Fin b)
  (hJ : IsUnit (V.submatrix id J)) : ...
```

Then:
- existing arbitrary theorem calls it with `exists_pivot_cols_of_rank`;
- new front theorem calls it with `J = frontEmbed` / `Fin.castLE`.

So: **additive and bounded in principle**. Expect Lean cast/rank bookkeeping, but no conceptual hidden dependency. The only trap is trying to prove equality about the old arbitrary `.choose`; avoid that.