**VERDICT:** TRACTABLE. The cleaner route dodges the `slotEquiv_BparamsLeaf_twoBlock` wall for the gate, provided you do not turn it into a full ambient partition problem.

The riskiest sub-goal is:

```lean
flat_schurFrameMap_slotReaderV0_eq_schurFrameProd
```

i.e. the entrywise theorem saying, for all `y`,

```lean
flat (schurFrameMap (slotReaderV0 y))
  =
schurFrameProd M (tach M) 1 h1 h2 1
  (readK y) (readX y) (readN y) (readE y)
```

up to the target `reindex`.

This is the cast/order bottleneck: top-left must be `K`, top-right `K * N`, bottom-left `X * K`, bottom-right `X * K * N + E`, at the exact `Fin.castAdd` / `Fin.natAdd` indices. But it is not the same wall as `slotEquiv_BparamsLeaf_twoBlock`: it only classifies rows and columns of one block matrix, not every ambient parameter coordinate into `V0 × V1`, and it has the four banked block-entry lemmas as direct witnesses.

For the gate, a free-standing

```lean
SchurInc t r c ≃ₗ[ℝ] Matrix (Fin (Text M (tach M) 1)) (Fin (Wext M 1)) ℝ
```

is not required. Cheaper: define a linear `flatL`, via `Matrix.fromBlocks` if available in Mathlib v4.29, verify-exists, or manually by a `Fin.castAdd` / `Fin.natAdd` case split. Then prove the needed identity by `Matrix.ext` plus the four block lemmas. A full `≃ₗ` only buys an inverse you do not need for this gate.

One correction: the chain-rule derivative of the matrix-valued layer should include `flatL`:

```lean
reindex_layer0 ∘L flatL ∘L schurFrameD (slotReaderV0 y₀) ∘L slotReaderV0
```

Unless `reindex_layer0` has been defined to absorb `flatL`. The V0-to-V0 statement can then project back to the SchurInc tuple coordinates, where the middle derivative is exactly the banked `schurFrameDeriv`.

Cheapest ordering:

1. Define `slotReaderV0 : (Fin routeMAmbient → ℝ) →ₗ[ℝ] SchurInc t r c`; prove four apply lemmas for `.K`, `.N`, `.X`, `.E`.
2. Define `flatL : SchurInc t r c →ₗ[ℝ] Matrix (Fin (t+r)) (Fin (t+c)) ℝ`; prove four block apply lemmas at `castAdd/castAdd`, `castAdd/natAdd`, `natAdd/castAdd`, `natAdd/natAdd`.
3. Prove `flatL (schurFrameMap z)` has the four expected blocks.
4. Compare with `schurFrameProd` using the banked block-entry lemmas.
5. Add the target `reindex_layer0` and banked `Agen = Cgen = schurFrameProd` collapse.
6. Apply the chain rule and reduce the V0 block to `schurFrameDeriv`; then use `schurFrameDeriv_det`.

The green-but-wrong proof can hide in slot order: especially swapping `N` and `X`, or using the wrong `natAdd` offset while casts still typecheck because dimensions coincide in this case. The check that catches it is an explicit off-diagonal probe:

```lean
-- top-right must depend on N:
(flatL (schurFrameMap (slotReaderV0 y)))
  (Fin.castAdd _ i) (Fin.natAdd _ j)
=
∑ k, readK y i k * readN y k j

-- bottom-left must depend on X:
(flatL (schurFrameMap (slotReaderV0 y)))
  (Fin.natAdd _ i) (Fin.castAdd _ j)
=
∑ k, readX y i k * readK y k j
```

If those two lemmas pass with the banked `schurFrameProd_block_KN/XK` lemmas, the cleaner route has not re-imported the full opaque ambient partition wall.