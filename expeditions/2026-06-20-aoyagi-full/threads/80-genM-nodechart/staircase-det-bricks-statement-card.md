# Statement card — direction-2 staircase det bricks + the assembly residual, `genm-detalpha`

The reusable linear-map-level bricks for the direction-2 staircase factorization of the unconditional
interior-det headline, plus the precise residual (the opaque-M cast-zone assembly). All bricks sorry-free,
clean-three, forced `#print axioms`.

## Brick A — the det-1 shear (`RouteMShearDet`)

> **Claim.** A unitriangular shear (det-irrelevant coupling) has determinant `1`: any endomorphism whose
> matrix is block-triangular under a grading with IDENTITY diagonal blocks has det `1`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.{blockTri_identityDiag_det_one, fderiv_det_one_of_shear}`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMShearDet.lean` @ `<off genm-detalpha c1a2e70f>`)
> - **Gloss.** `blockTri_identityDiag_det_one`: `M.BlockTriangular b` + `(b i = b j → M i j = if i=j then 1
>   else 0)` ⟹ `det M = 1`. `fderiv_det_one_of_shear`: the fderiv-level form (`|det D| = 1`).
> - **Proved (unconditional, sorry-free, clean-three).** Abstracts `RouteM222Det.shear222Deriv_det`'s tail
>   to any grading / opaque width. The 2-value `{modified}/{kept}` grading is an ENDOMORPHISM grading, so it
>   sidesteps the L-value partition wall (`RouteMGradingObstruction`).
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free, clean-three — awaiting reviewer.

## Brick B — the staircase det spine (`RouteMStaircaseDet`)

> **Claim.** A block-lower-triangular endomorphism's det is the product of its diagonal-block dets (the
> couplings det-irrelevant), iterated `lowerTri`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.lowerTri3_det`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMStaircaseDet.lean` @ `<off genm-detalpha c1a2e70f>`)
> - **Gloss.** `det (lowerTri f₀ (lowerTri f₁ f₂ h₁₂) (inl∘h₀₁ + inr∘h₀₂)) = f₀.det · f₁.det · f₂.det`
>   (the 3-block staircase, two `RouteMSchurFrameDet.lowerTri_det` peels).
> - **Proved (unconditional, sorry-free, clean-three).** The `prodEquivOfIsCompl` /
>   `det_eq_det_mul_det`-on-an-invariant-subspace gluing (each peel at the linear-map level, in/out bases
>   may differ) — the named escape from the single-grading `BlockTriangular` partition wall.
> - **Assumed / Cited.** none.
> - **Deferred.** the general `Fin L`-fold staircase (the 3-block template generalizes by induction
>   reusing `lowerTri_det`; the assembly applies `lowerTri_det` per layer at the concrete depth).
> - **Status.** sorry-free, clean-three — awaiting reviewer.

## The remaining assembly (the precise residual — the opaque-M cast-zone)

The unconditional headline `|det Dφ_M| = |u_p|^{minAdm−1}·∏_s(|det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s−1−i)})`
needs the ASSEMBLY connecting the real chart `D(T_M)` to the banked bricks. Verify-first CONFIRMED the
factorization realizes (already proven at both anchors: `phi222_abs_det`, `phi3333_abs_det`). The bricks
banked this leg + the pre-banked engine make every step's TOOL available:

| sub-task | status | tool |
|---|---|---|
| per-layer `DC_s` det = engine value | **DONE (pre-banked)** | `schurFrameD_abs_det`, `lduCoreD_abs_det`, `radial_abs_det_minAdm` |
| det-1 shear | **DONE (Brick A)** | `fderiv_det_one_of_shear` |
| staircase spine (det = ∏ diag) | **DONE (Brick B)** | `lowerTri3_det` / `lowerTri_det` iterated |
| value-locality → det product | **DONE (prior leg)** | `fderiv_abs_det_eq_prod_diagBlocks` |
| **(1) `shear_M` def + (3) `pack_M ∘ T_M = chartParamsGen` bridge** | **RESIDUAL** | — |

**The residual is sub-tasks 1+3 — the opaque-width `chainA`/`Agen`/`paramsEquivFlat` cast zone:**

- `chainA(N,W,C) = reindex [[C − N·W],[W]]` (`RouteMChainBlock`); `chainQ(N) = [I | N]`;
  `Cgen = B·chainQ(N) + u·R`. The FULL differential of `chainA` w.r.t. `(N, W, C)` carries the bilinear
  `−dN·W − N·dW` shear. The validated structure places `−dN_s·W_s` STRICTLY OFF the layer-`s` diagonal
  block (it couples to the PREVIOUS layer's pivot, since `N_s ∈ C_s` whose pivot is in `A_{s-1}`). Banked
  `chainUnitMap` (`RouteMGenChainBridge`) handles only the FROZEN-`N` part (`(W,C) ↦ (W, C−N·W)`, det 1) —
  the genuine `−dN·W` shear (when `N` is also a coordinate) is the new content.
- The bridge `pack_M ∘ T_M = chartParamsGen` is the opaque-M generalization of `(2,2,2)`'s
  `chartParams222_eq_pack_T` (which leaned on `T222_apply`'s explicit 8-vector) — it needs the general
  `chartParamsGen ⟨s⟩ = reindex (Agen s)` expansion over opaque `Text`/`Wext` widths, the dependent-`Fin`
  reindex zone the CLAUDE.md gotchas + Codex flag as the cost driver.

**This residual is a genuine multi-tide construction in the cast-heavy zone, not a ≤4-attempt closure.**
The bricks make the LINEAR-ALGEBRA and DET steps bounded; what remains is the FAITHFUL expression of the
real `D(T_M)` as `(radial/spectator pivots) ∘ (the −N·W staircase shear)` over opaque widths — the
`Frame3333Deriv`/`shear222` hand-machinery generalized (at `(2,2,2)` ~200 lines; opaque-M is more). The
controller flagged splitting this into a dedicated cast-specialist tide.
