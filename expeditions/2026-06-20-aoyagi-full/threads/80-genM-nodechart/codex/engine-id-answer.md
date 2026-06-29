Short verdict: **bank the Schur value recognition first**, but bank it in **block-split coordinates**, not as a raw global matrix equality. Then use it to identify the fderiv by chain rule against the already-banked `schurFrameMap_hasFDerivAt` / `lduCoreMap_hasFDerivAt`.

**1. Next Bank**
Use a theorem of this shape:

```lean
frameOut (Cgen u M t B hle s)
  = schurFrameMap (K_s, N_s, X_s, u • E_s)
```

where `frameOut` is the output block CLE/equiv
`Matrix (Fin (Text s)) (Fin (Wext s)) ℝ ≃L SchurInc t r c`.

Do **not** start with a raw

```lean
Cgen s = Matrix.fromBlocks ...
```

unless it is only a corollary. The lower-risk proof grain is:

- define `frameOut` using the same row/column split orientation as `bmatStack`, `rmatPad`, and `chainQ`;
- prove four block lemmas: `K`, `KN`, `XK`, `XKN+uE`;
- inside each block lemma, use `ext i j` and the banked accessor lemmas.

So: **per-block theorem statements, per-entry proofs inside them**. Avoid one giant `ext i j` over arbitrary opaque `Fin (Text s)` / `Fin (Wext s)`.

**2. Fderiv Identification**
Yes: prove the identification **one boundary at a time**. Make local input/output coordinate equivalences first, then assemble globally.

The main caution: as currently described, `SchurInc` has a raw matrix `K` slot, while `lduCoreDeriv` lives on `LDUParam t`. In Lean this will not literally type as

```lean
schurFrameDeriv X K N ∘ lduCoreDeriv
```

without an adapter. Least-risk choice:

```lean
abbrev FrameParam t r c :=
  LDUParam t ×
    (Matrix (Fin t) (Fin c) ℝ ×
      (Matrix (Fin r) (Fin t) ℝ × Matrix (Fin r) (Fin c) ℝ))
```

then define a local CLE `FrameParam ≃L SchurInc` using `matrixSplit.symm` on the `K` slot and identity elsewhere. The engine block is then a conjugated map on `FrameParam`:

```lean
raw.symm ∘ schurFrameDeriv X K N ∘ raw ∘
  (lduCoreDeriv l q u on K-slot, id on N/X/E)
```

The conjugating `raw.symm ∘ raw` cancels in determinant. This is much safer than pretending `LDUParam` and `Matrix` are interchangeable.

The `lowerTri` nesting helps for determinant and sanity checks. For fderiv equality, use `schurFrameDeriv_apply` / `chainAFDeriv` coordinate formulas. Do not expect the nested `lowerTri` definitions to rewrite directly against `Agen`; `Agen` also includes the chain shear `[C - N·W ; W]`.

**3. Staircase vs Bypass**
The two-sided staircase conjugacy is still the sound assembly target.

The old locality shortcut fails for the stated reason: one common row/column grading does not exist for the real flat chart partitions. A per-layer `HasFDerivAt` plus “restricted diagonal determinant” is not enough unless those restrictions are square blocks in a common endomorphism decomposition.

A `det_comp` bypass is only viable if you build a genuine global factorization by full-space endomorphisms, e.g. a `composeFold` of conjugated factors. But proving that fold equals the real chart is essentially the same cast problem as building `eIn/eOut`, and usually worse because it requires value equality of the whole nonlinear map. Since `interiorDet_headline_of_twoStairConj` is banked, feed it.

**4. `V`, `eIn`, `eOut`**
Yes, global `eIn/eOut : (Fin N → ℝ) ≃L StairProd V (L+1)` is likely the largest cast cost. Do not build it by hand from `Fin N`.

Use the existing spine:

- `paramsEquivFlatCLE` / `bridgeCLE`;
- `chartIdxEquiv`;
- `flatToChartIdxCLE`;
- `sumPiEquivProdPi`;
- `frameSplitEquiv`;
- local matrix/tuple split CLEs.

Also reconsider `V (s+1) = SchurInc t r c`. If the K coordinate is LDU-parametrized, use `FrameParam t r c` as `V (s+1)`, with a local raw-Schur conjugacy for the Schur derivative. That avoids a recurring `Matrix`/`LDUParam` adapter at every layer.

**Risk Ranking**
Highest cast risk:

1. Global `eIn/eOut` into dependent `StairProd V`.
2. Output-side `Agen` to staircase wiring, including chain shears and the `s`/`s+1` shift.
3. K-slot raw matrix vs `LDUParam` coordination.
4. `Cgen = Schur frame` value identity over opaque widths.
5. Boundary fderiv identification after the value identity.
6. Determinant computations once the maps type.

Least-risk next bankable target:

```lean
frameOut_Cgen_eq_schurFrameMap
```

for one arbitrary interior boundary, stated in split `SchurInc`/`FrameParam` coordinates, proved by four block accessor lemmas. That theorem will make the fderiv identification a chain-rule/congruence problem instead of a global reindex fight.