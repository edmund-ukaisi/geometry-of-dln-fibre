# Statement card — general-`L` smeared box supplier: R1 dets (the distinguished-path det theorem) LANDED

**Status:** R1 (the two box determinants `hGram`/`hGram0`/`hWaist`) is discharged **at the engine
level, sorry-free**, on `origin/genm-smearbox` (based on `origin/genm-smeardata @9bc9aa0e`). Axiom
footprint `[propext, Classical.choice, Quot.sound]` — pure matrix algebra, NO `sorryAx`, NO
`native_decide`, NO `monomial_rlct`. Three new modules (2 Core engine + 1 DLN connector), all green
(8339 jobs). Aggregator wiring left for the controller.

This CLOSES **Residual 1** of the `genm-smeardata` statement card (the general-box cross-term
determinant theorem — flagged there as "large-but-STANDARD … hardest step = the path-expansion
cross-term bound for arbitrary widths"). The distinguished-path bound is the branch the design
certificate (`/tmp/r1design/codex-answer.md`) called "the single hardest step".

## What is proved (R1, the distinguished-path determinant theorem, ∀L)

The design's distinguished-path/leakage estimate, made **inductive** over a two-sided entrywise
invariant (avoids `det(∏)=∏det` leakage; the certificate's Collapse-2 Cauchy-Binet is sidestepped by a
direct full-column-rank route).

### `DLNFibre/Core/Matrix/CarrierBlock.lean` (network-free engine, sorry-free)
- `CarrierBound P dlb oub` + `CarrierBound.strictRowDominant` / `.det_ne_zero` — an `r×r` block with
  carrier diagonal `≥ dlb`, off-diagonal `≤ oub`, and `(r−1)·oub < dlb` is strictly row-dominant
  (Levy–Desplanques, via banked `StrictRowDominant.det_ne_zero`).
- `WideCarrierBound P r dlb nb pub` — the wide invariant on the first `r` rows of an `h×w` partial
  product (carrier diag `≥ dlb`, non-carrier-diag `≤ nb`, all `≤ pub`); `CarrierLayer A r δ η` — a
  layer with carrier diag `∈ [δ/2,δ]`, everything else `≤ η`.
- **`wideCarrier_mul` (THE CRUX, de-risked at n=2 first)** — the one-step composition: advancing
  `WideCarrierBound` across one `CarrierLayer` via the linear recursion `dlb' = dlb·(δ/2) −
  (w−1)·pub·η`, `nb' = nb·δ + w·pub·η`, `pub' = w·pub·δ`. The distinguished-path term isolation with
  `.val`-uniform carrier-index bookkeeping (`kd = ⟨i,hiw⟩`); the cast is SOUND (no research wall).
- `WideCarrierBound.carrierBlock` — extract the `r×r` `CarrierBound` from the wide invariant.

### `DLNFibre/Core/Matrix/GramFullRank.lean` (network-free engine, sorry-free, Mathlib-only)
- `gram_det_ne_zero_of_submatrix_det_ne` — `det(PᵀP) ≠ 0` from a nonzero `r×r` minor of a tall `P`
  (`rank P = r` via the minor, `rank(PᵀP) = rank P` by `Matrix.rank_transpose_mul_self`, square full
  rank ⟹ `det ≠ 0`). The Collapse-1 full-column-rank route.
- `right_factor_det_ne_of_rank_eq` — `P = U·W`, `rank P = r`, `W` square ⟹ `det W ≠ 0`
  (`rank_mul_le_right`). Powers `hWaist`.
- Small `det ⟺ rank` bridges reproduced locally (duplicate `Core.RankLocusClosed`'s, avoid the quiver
  stack import).

### `DLNFibre/DLN/RLCT/Validate/RouteMSmearedBoxGen.lean` (DLN connector, sorry-free)
- `carrierLayer_reindex` — `CarrierLayer` survives the `prodAux` `finCongr` recast (`.val`-preserving).
- **`wideCarrierBound_prodAux`** — iterates `wideCarrier_mul` over the `prodAux` fold (induction on
  `k`, from the identity base), with the **Codex-designed fused invariant** (`nb ≤ η·Acc`,
  `dlb ≥ (δ/2)^k − η·Acc`, `Acc ≥ 0`; `Acc` absorbs the growing `pub`). Requires only the free front
  layers `t.val < L−1` to be `CarrierLayer`s (matches `frontProd = prodAux(L−1)`).
- `dominance_of_small_eta` + `carrierBlock_prodAux_det_ne` — the small-`η` closer
  (`r·η·Acc < (δ/2)^{L−1}` ⟹ `(r−1)·nb < dlb`) gives `det ≠ 0` on the `frontProd` carrier `r×r` block.
  Existential `Acc` for the box supplier to pick `η` against.
- `P1uG_submatrix_eq_carrierBlock` — `deepWidthEquiv(inl) = first-r columns` (item-123 exponent-sound),
  so `P1uG`'s carrier `r×r` minor IS the `frontProd` carrier block.
- **`gram_det_ne_of_carrierLayers`** — `hGram`/`hGram0`: `det((P1uG u)ᵀ P1uG u) ≠ 0` from
  `frontTupleG u`'s front layers being `CarrierLayer`s + small `η` (z-free, so `hGram0` at `z=0` is the
  same application).
- `boxGen` / `slotBoxGen` / `boxGen_coordOfG` / `measurableSet_boxGen` — the box231-generalization: front
  carrier-diag `∈ [δ/2,δ]`, everything else `∈ [−η,η]`; measurable.
- `frontTupleG_carrierLayer_of_boxGen` — `frontTupleG u`'s free front layers are `CarrierLayer`s when
  the front-slot coords lie in `boxGen`.
- **`waist_det_ne_of_gram`** (+ `P1uG_eq_mul_Vrho`) — `hWaist`: `det(V[:,ρ]) ≠ 0` for any width-`r`
  factorization `frontProd = U·V`, as the certificate corollary of `hGram` (`P₁ = U·V_ρ`, rank `r` ⟹
  `V_ρ` unit).

## Item-123 fidelity (verified)
- The carrier corridor `ρ = deepWidthEquiv ∘ inl` IS the first-`r` injection (`.val`-preserving,
  `finSumFinEquiv_apply_left`) — confirmed. The front slots are `∉ topCoordsG` (they live at
  `t.val < L−1`, `topCoordsG` at `t = L−1`), so conditioning them near `δ` leaves the radial exponent
  `= r·c` unchanged. `slotBoxGen`'s diagonal branch fires only for front layers (`q.1.1.val < L−1`).
- The distinguished-path `.val`/cast bookkeeping is machine-verified sound (the n=2 de-risk built
  first, then scaled); no fabricated box, no fabricated path bound.

## What remains for the fully-unconditional `hSmeared ∀L` (precise gap)

### Residual 2 — the general-`L` Field-A entry bound `hSpre` (NOT built)
No general-`L` analog of the L=2 `condBox_subset_preimage` yet. Bounds each decoded flat entry of
`psiMapG (RmapG u)` by `2δ` (to land in `cubeBox ε`): front entries are products of `≤ L−1` coords
(`≤ δ^{L−1}`), `Λ₀` entries via the Varah inverse bound (`StrictRowDominant.inv_mul_entry_bound`,
banked in `Core.Matrix.DiagDominance`), `z·H̄`/`S_bot` linear. `genDecode_params` gives the flat
structure; the residual is the entrywise bound through the decode. **~200 lines**, comparable to the
L2 `RouteMSmearedSquareL2` Field-A block. This is the blocker for the assembly.

### Assembly — feeding `smearedChartDataGen_of_dets`
`hRinj` and `hboxpos` are **BUILT** (`RmapG_injOn_condBox`, `boxGen_pos`, both sorry-free). Remaining:
(a) relate `boxGen` (indexed `Fin(routeMAmbient M)`) to `box₀ : Fin(n+1)` via `hN`, deriving the
front-coord conditioning `hu` (for `frontTupleG_carrierLayer_of_boxGen`) from `condBox`-membership;
(b) pick `η* ≤ (δ/2)^{L−1}/(r·Acc)` explicitly (needs `Acc` exposed as a closed form OR the existential
`carrierBlock_prodAux_det_ne` returns threaded through — the existential form is already there, so this
is picking `η*` inside the box supplier); (c) instantiate `smearedChartDataGen_of_dets` with `boxGen` +
the discharged hyps → `smearedChartGen` → the unconditional `hSmeared ∀L`. Also needs the structural
extraction (`r`,`s`,waist `q`,`hminadm`,pivot `hp`) from `BoundarySmeared`, a separate wiring.

The BLOCKER for (c) is `hSpre` (Residual 2). Everything else in the assembly is now a clean hop.

## Reusable value banked NOW
The distinguished-path determinant theorem (`CarrierBlock` + `GramFullRank`) is a **network-free,
axiom-clean engine** reusable for ANY carrier-block product dominance argument. R1 (`hGram`/`hGram0`/
`hWaist`) is fully discharged from a concrete `boxGen` at any depth — the certificate's crux is closed
as a machine-checked reduction. Only R2 (Field-A) + the mechanical assembly remain.
