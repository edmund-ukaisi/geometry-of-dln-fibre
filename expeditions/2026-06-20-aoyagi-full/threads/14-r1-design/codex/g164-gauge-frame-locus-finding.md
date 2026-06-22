# g164 — the gauge-frame locus: gaugeDecode/regAbsorb must apply a NON-trivial frame (option a), and it carries B's rank factors

The gauge frame for the deepest point is NOT trivial, and it lives in `gaugeDecode`/`regAbsorb`
(option a), not in `split` (which must stay MP). Grounded in `deepestPoint_exists`'s actual
construction, NOT the cert's idealization.

## What `deepestPoint` actually IS (Skeleton.lean `deepestPoint_exists`)

For `r > 0, L ≥ 2`, the deepest point is `wLayers H r U V` where:
- `U = P⁻¹ · embM` and `V = projM · Q⁻¹` are the rank-`r` factors of `B = U·V` (from
  `block_elimination H r B`), general rank-`r` matrices;
- the boundary layers carry `U` and `V`: layer 0 `= U · [I_r|0]` (`H 0 × H 1`), layer `L−1` involves
  `V`; middle layers `= corM` (the corner block `[[I_r,0],[0,0]]`).

So `deepestPoint` is rank-`r`-exact (`IsDeepLayers`) but its boundary layers are `U·…`, `…·V` with
`U, V` general rank-`r` — NOT the block-normal `[[I_r,0],[0,0]]`. The cert g125's "identity corners,
no gauge needed" is an IDEALIZATION (or a differently-constructed point); the Lean `deepestPoint`
genuinely carries the `U, V` boundary frames.

## Consequence: the gauge frame is real, non-trivial, and lives in gaugeDecode (option a)

The `(X_s, Y_s, Z_s, T_s)` blocks are the deviation of layer `s` from its deepest value, expressed in
a frame that block-normalizes the deepest layers. With `deepestPoint`'s boundary layers `= U·…`,
`…·V`, the frame must include `U⁻¹`/`V⁻¹`-type boundary corrections (the `P, Q` of
`block_elimination`). So:

- **(a) is forced:** `gaugeDecode q = roleSplit ∘ (per-layer frame applied to (split.symm q))`, the
  frame a FIXED per-layer GL conjugation (continuous linear iso, basepoint-preserving since the
  framed deepest layer is block-normal). `split` stays the MP index reindex (det = ±1; crux2's
  `split_mp` proof unaffected).
- **(b) is WRONG:** baking the frame into `split` breaks `split_mp` — the gauge frame `P_s, Q_s`
  (`= P⁻¹·embM`, `projM·Q⁻¹`) has det ≠ ±1 in general, so a frame-incorporating split is not
  measure-preserving. The frame's non-MP-ness is exactly why it belongs in the absorption layer
  (where the RLCT machinery peels the bounded-unit Jacobian), NOT in the MP `split`.

## The blocker this surfaces

The frame terms (`P, Q, U, V` from `block_elimination`/`deepestPoint_exists`) are currently BURIED
inside `deepestPoint_exists`'s `Classical.choice` — not exposed as accessible Lean terms. To build
`gaugeDecode`/`regAbsorb` I need the per-layer deepest-point frame exposed (the `P_s, Q_s` with
`P_s · (deepestPoint s) · Q_s = blockdiag[I_r, 0]`, or equivalently the layer's
already-block-normalizing conjugation). This is a Skeleton-level exposure (crux2 single-writer):
either expose the frame from `deepestPoint_exists`, or provide a lemma `deepestPoint_frame_exists`
giving the per-layer `(P_s, Q_s)` units. Asked crux2.

## Why this matters (not a detour)

This is the load-bearing geometric content the squeeze rests on: `loss = ‖∏A_s − B‖²` in raw coords
equals `‖U_bdry · (∏C_s − blockdiag[I,0]) · V_bdry‖²` in framed coords (interior frames telescope,
`Q_s P_{s+1} = I` by compatible choice), comparable to `‖∏C − blockdiag[I,0]‖²` up to the bounded
invertible boundary factors `U_bdry, V_bdry`. Those bounded factors are part of the squeeze constants
`c₁, c₂`. So the frame is not cosmetic — getting its locus right (a, in gaugeDecode) is what makes
the squeeze well-posed.
