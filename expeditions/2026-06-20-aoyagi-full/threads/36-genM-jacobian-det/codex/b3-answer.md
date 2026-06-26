**Verdict:** step 3 is not logically unavoidable as a *map equality*, but its mathematical content is unavoidable. A derivative-only proof can replace

`chartParamsFlat = flat-frame-product`

by

`D chartParamsFlat = derivative-of-flat-frame-product`

but that is the same opaque-width `chainA`/frame reconciliation at derivative level.

A few concrete points from the current worktree:

- `general_composed_clm_abs_det` only telescopes a list of full-ambient CLMs once you already have them and their dets. It does not build the ambient embeddings, prefix derivatives, or prove the actual chart derivative is that list product. See [RouteMAchieverGeneralDet.lean](</home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-ab65ad6d0ec4aad88/lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverGeneralDet.lean:85>).
- `RouteMGenChainBridge` already says the right thing: the `chainA`/`chainQ` entry laws and `chainUnit_det` are bounded bricks, while full `phiFlat_abs_det` still needs the prefix scaffold plus global chart-equality over opaque widths. See [RouteMGenChainBridge.lean](</home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-ab65ad6d0ec4aad88/lean/DLNFibre/DLN/RLCT/Validate/RouteMGenChainBridge.lean:19>).
- The current `genBlkFlat` uses modular `flatIdxOf`, so it is rate-side scaffolding, not yet a determinant-ready bijective coordinatization. A determinant theorem for the literal modular decoder is not the right target until that is replaced by a genuine packing/splitting. See [RouteMGenFlatChart.lean](</home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-ab65ad6d0ec4aad88/lean/DLNFibre/DLN/RLCT/Validate/RouteMGenFlatChart.lean:57>).

For Q1: the block-triangular direct route is mathematically viable, but not a real shortcut. Once you grade coordinates by boundary and role, the dependency direction is triangular/banded: `A_s = chainA(N_s,W_s,C_{s+1})`, so later boundary data feeds earlier layer output through `C_{s+1}`; the radial variable feeds many rows and must be ordered as its own exceptional block. The diagonal blocks should be conjugates of the Schur/LDU/chain/radial Phase-A derivatives. But proving those diagonal-block identifications requires exactly the same `Fin N ≃ Σ boundary, role` split and `chainA_apply_castAdd/natAdd` reconciliation.

For Q2: I would not make generic `Matrix.BlockTriangular` the spine. In Lean, the general variable-width block-triangular route will force you to prove the grading image, identify each fiber `{i // grade i = a}` with a dependent matrix/product space, and assemble a product over those fibers. That is at least as much work as full-ambient factors, and probably worse. The `(3,3,3,3)` proof works this way because the grading is finite and concrete; the general opaque-width version is a different order of bookkeeping. The fixed case closes by first proving `phi3333 = Q ∘ T`, then `T = Frame ∘ Kparam`, then using `det_comp`; see [RouteM3333Atom.lean](</home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-ab65ad6d0ec4aad88/lean/DLNFibre/DLN/RLCT/Validate/RouteM3333Atom.lean:469>).

For Q3: yes, the honest call is (i), with one clarification. Bank a `ChartFactor`/prefix-fold scaffold because that is bounded and reusable: it should turn nonlinear factors plus prefix points into a derivative list and then feed `general_composed_clm_abs_det`. But report the real residual as:

1. determinant-ready flat coordinatization, not modular `flatIdxOf`;
2. full-ambient conjugates of Schur/LDU/chain/radial factors;
3. the chart/derivative equality tying `chartParamsGen ∘ genBlkFlat` to that factor product over opaque `Wext`/`Text`;
4. exponent bookkeeping into `leafH`.

The true bottleneck is **the opaque-width chart reconciliation**: proving the actual `chainA`-built chart has the same block coordinates, or same derivative blocks, as the flat-frame factorization. The determinant algebra is already essentially done; the full-ambient/factor equality is the multi-pass part.