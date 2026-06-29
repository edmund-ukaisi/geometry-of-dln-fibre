# Coarse-route grading obstruction — the single-grading `BlockTriangular` route is BLOCKED

Surfaced while commissioning the COARSE-route unconditional interior-det headline (controller leg on
`genm-detalpha`). Verify-first (concrete `(2,2,2)` count + a decorrelated Codex read) before the
`BlockTriangular` build — and it walls. This is a knowing-decision recalibration, not a thrash.

## The claim that fails

The commission: grade `Fin N` by a COARSE boundary-level grading `g` (radial 0 + one grade per boundary),
prove `D(T_M).BlockTriangular g`, feed `interiorDet_headline_of_blockTri`. `Matrix.BlockTriangular`
(Mathlib v4.29) takes a **single** grading `g : Fin N → ℕ` shared by rows (output coords) and columns
(input coords) — no asymmetric (row-grading ≠ column-grading) variant exists.

For the interior frame `D(T_M)` (endomorphism of `Fin N → ℝ`), a single grading needs the OUTPUT-coord
layering and the INPUT-coord layering to be the SAME function `g`. They are two different partitions:

- **INPUT** coords graded by `bLayer` = the `chartIdxEquiv` boundary: layer `s` carries
  `schurDim s + liftDim s` coords (Schur `K/X/N/E` + lift `W` of boundary `s`).
- **OUTPUT** coords graded by `paramsEquivFlat` / `FlatIdx` layer (the chart output is
  `paramsEquivFlat (chartParamsGen …)`, `chartParamsGen ⟨s⟩ = Agen s` flattened to FlatIdx layer `s`):
  layer `s` carries `M_s · M_{s+1}` coords.

A single grading needs a bijection `e : Fin N ≃ FlatIdx` with `FlatIdx-layer ∘ e.symm = bLayer`, hence
the PER-BOUNDARY counts must agree: `schurDim s + liftDim s = M_s · M_{s+1}` for every `s`.

## The hard evidence (banked, `(2,2,2)`)

`RouteMGradingObstruction.flatLayer_ne_chartBoundary_222` (sorry-free, `decide`, clean-three):

| partition | boundary/layer 0 | boundary/layer 1 | total |
|---|---|---|---|
| **FlatIdx layer** (`M_s·M_{s+1}`)        | 4 | 4 | 8 |
| **ChartIdx boundary** (`schurDim+liftDim`) | 6 | 2 | 8 |

`(4,4) ≠ (6,2)`. Only the TOTALS agree (`chartDim_eq_flatDim`). The lift `W_s` of boundary `s` (size
`(M_{s+1}−t_{s+1})·M_{s+2}`) is counted at INPUT-boundary `s` but its weight lands in a DIFFERENT output
layer. **No layer-aligned bijection exists, even coarse.** The obstruction is mathematical (the two
filtrations of `Fin N` are genuinely incompatible), not a Lean-cast artifact.

## Why (the structural reason)

`Agen s = chainA(N_s, W_s, C(s+1))` is the output flat-layer-`s` block; the locality
(`Agen_genBlkFlatLiveR1_reads_le`) gives "output flat-layer `s` reads input `bLayer ≤ s`" — genuinely
one-sided. But a coordinate `i` plays DIFFERENT roles as row (output, FlatIdx layer) vs column (input,
bLayer), and `BlockTriangular` forces ONE grade per index. With the partitions incompatible, no `g`
makes `g j < g i ⟹ entry (i,j) = 0` hold while keeping square diagonal blocks. The natural block
structure is RECTANGULAR/STAIRCASE (output-layer-`s` block × input-boundaries-`≤ s`), which
`Matrix.BlockTriangular` does not express.

## Route status (both banked routes walled)

- **Route α (this obstruction):** square `BlockTriangular` under one grading — BLOCKED (no layer-aligned
  bijection; partition mismatch proven). The value-locality (`fderiv_abs_det_eq_prod_diagBlocks`,
  `Agen_…_reads_le`) is real and banked, but it factorizes the det over the `toDual∘bLayer` grading on a
  matrix whose diagonal blocks (under bLayer) are NOT the engine Schur/LDU blocks — because the output
  the bLayer-`s` rows produce is not the Agen-`s` block.
- **Route β (composeFold, controller-declared dead as-banked):** the banked `chainChartFactor` is linear
  with frozen `Nblk`; its `composeFold` matches `phiGen`'s value/det at a point but differs as a MAP
  (Jacobian misses the `−dN_k·W_k` shear). A β-rebuild needs a new NONLINEAR chain factor + a re-derived
  det-1 + a `ρ_in/ρ_out`-dependent-`Fin` reindex.

## Recommendation (constructive — for the controller)

The unconditional headline `|det Dφ_M| = u^{minAdm−1}·∏_s(…)` needs a NON-`BlockTriangular`
factorization. Two viable directions, both genuine new work (neither is a bounded cast-cleanup):

1. **Re-derived nonlinear chain factor (the β-rebuild).** Build the genuinely-bilinear per-boundary
   chart factor (carrying the `−dN_k·W_k` shear), prove its `det = 1`, and telescope `det_comp` over the
   chain. This is the route the (3,3,3,3) `Frame3333Deriv`/`Kparam3333Deriv` hand-machinery realises
   concretely (`frameB`, 13 SCC blocks); generalising it to opaque `M` is the substantial piece.
2. **Rectangular/staircase det.** Express `D(T_M)` as a product of an output-FlatIdx-graded
   lower-triangular factor (the chainA shears, det 1) and a block-DIAGONAL factor whose blocks ARE the
   per-boundary Schur⊗LDU differentials — i.e. build the staircase decomposition by hand at the linear-
   map level (à la `Core.FibreNormalForm`'s `prodEquivOfIsCompl` gluing), NOT via Mathlib
   `BlockTriangular`.

Either is a fresh expedition leg, not a continuation of the de-risked locality. The banked
`fderiv_abs_det_eq_prod_diagBlocks` + the role grading remain reusable for direction 2's diagonal-block
det reads. The `interiorDet_headline_of_blockTri` conditional headline is still the correct TARGET shape
— what's missing is a sound way to discharge its `hbt`/`hR`/`hB` on the real frame, and that way is NOT
a single-grading `BlockTriangular`.

## Banked this leg

- `lean/DLNFibre/DLN/RLCT/Validate/RouteMGradingObstruction.lean` — the `(2,2,2)` partition-mismatch
  witness (`flatLayer_ne_chartBoundary_222`, `flatTotal_eq_chartTotal_222`), sorry-free clean-three.
