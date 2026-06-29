# Statement card — route-α role-grade refinement + locality⟹det bridge, `genm-detalpha`

Two banked bricks from the route-α tide (the de-risked "heart"): the **role-grading refinement** of the
proven `bLayer` value-locality, and the **reusable locality⟹det bridge** composing the two banked levers.

## Brick 1 — the role-grade refinement (`RouteMRoleGrade`)

> **Claim.** The proven `bLayer` value-locality refines to a **role grading** `bRole = 2·bLayer + (1 if
> lift-role else 0)` that separates, within each boundary layer `k`, the Schur-frame role (`K/X/N/E`
> coords, `chartIdxEquiv ↦ ⟨k, Sum.inl ·⟩`) from the lift role (`W` coords, `↦ ⟨k, Sum.inr ·⟩`); each
> reader is invariant under changing `x` away from its OWN role at its layer (strictly stronger than the
> `bLayer`-level `read*_indep_of`), and the two roles are disjoint (zero within-layer 2-cycles).
>
> - **Lean:** `DLNFibre.DLN.RLCT.{bRole, isSchurRole, isLiftRole, bRole_div_two, bLayer_le_of_bRole_lt,
>   readK_indep_of_role, readX_indep_of_role, readN_indep_of_role, readE_indep_of_role,
>   readW_indep_of_role, not_schur_and_lift}`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMRoleGrade.lean` @ `<pending — off genm-detalpha (base b78358a5)>`)
> - **Gloss.**
>   - `bRole` / `isSchurRole` / `isLiftRole`: the role grading and the Schur/lift role predicates, read
>     off `chartIdxEquiv`'s `Sum.inl`/`Sum.inr`.
>   - `bRole_div_two`: `bRole q / 2 = bLayer q` — `bRole` is a genuine refinement (the parity bit is the
>     only added information; the layer is recovered).
>   - `bLayer_le_of_bRole_lt`: `bRole i < bRole j → bLayer i ≤ bLayer j` — the role order extends the
>     layer order (no reversal; a finer grading).
>   - `read{K,X,N,E}_indep_of_role`: each Schur reader of boundary `k` is invariant under changing `x`
>     away from the Schur role of layer `k` (`∀ q, bLayer q = k → isSchurRole q → x q = y q`).
>   - `readW_indep_of_role`: dually for the lift reader (lift role).
>   - `not_schur_and_lift`: no coordinate is both Schur- and lift-role.
> - **Proved (unconditional, sorry-free, clean-three `[propext, Classical.choice, Quot.sound]`).** All
>   eleven, value-level (finite equivalences; `chartIdxEquiv.apply_symm_apply` + `Sum.isLeft/isRight`).
>   No fderiv, no flattening.
> - **Assumed.** `StructAdm M t` (the structured-decoder admissibility, as in all sibling reader lemmas).
> - **Cited.** none.
> - **Deferred.** the OUTPUT-side analogue (an `Agen`-level role-locality, refining
>   `Agen_genBlkFlatLiveR1_reads_le`) — only needed if the FINE role grading is taken; per the route
>   adjudication the COARSE grading is preferred (see below), so this refinement is INPUT-side
>   infrastructure, not on the immediate critical path.
> - **Status.** sorry-free, clean-three (forced `#print axioms`) — reviewed (fidelity verdict
>   *survived*; two report-only docstring sharpenings applied: the `RouteMLocalityDet` "in one shot"
>   phrasing now states the small `toDual`-transport wrapper to use it WITH the headline; the
>   `FlatIdx ≃ ChartIdx` phrase now notes the raw per-layer sizes differ so the honest common grading is
>   the COARSE boundary-level one).

## Brick 2 — the locality⟹det bridge (`RouteMLocalityDet`)

> **Claim.** For any differentiable self-map `f` of `Fin N → ℝ` with value-locality (`g i < g j ⟹ output
> i invariant under input j`), the Jacobian abs-det factorizes as the product of the diagonal-block
> abs-dets — UNCONDITIONALLY (no per-block-det input, no map equality). The clean composition that was
> missing between the two banked route-α levers.
>
> - **Lean:** `DLNFibre.DLN.RLCT.fderiv_abs_det_eq_prod_diagBlocks`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMLocalityDet.lean` @ `<pending — off genm-detalpha (base b78358a5)>`)
> - **Gloss.** Given `HasFDerivAt f D u` and `hloc : ∀ i j, g i < g j → (∀ k ≠ j, v k = u k) → f v i =
>   f u i`, then `|det D| = ∏_{a ∈ image (toDual∘g)} |(toMatrix' D).toSquareBlock (toDual∘g) a).det|`.
>   Composes `toMatrix_blockTriangular_of_locality` (block-tri from locality) with the abs form of
>   `Matrix.BlockTriangular.det` (over `ℕᵒᵈ`, a `LinearOrder`).
> - **Proved (unconditional, sorry-free, clean-three).** The det-factorizes-by-grade fact; in-file
>   non-vacuity on a constant map.
> - **Assumed.** none (`hloc` is supplied by the caller).
> - **Cited.** none.
> - **Deferred (the route-α RECALIBRATION — the honest ceiling).** This bridge discharges the headline's
>   `hbt` + the abs `BlockTriangular.det` step in ONE shot, BUT the FULL unconditional headline on the
>   REAL chart `phiFlatLiveR1` is NOT reached by route-α's de-risked locality alone. Two pieces remain,
>   neither covered by the "DAG-topological, bounded" de-risking and both confirmed by a decorrelated
>   Codex read:
>   1. **`paramsPack_layer` (a genuine bounded-but-nontrivial construction).** The chart's INPUT grading
>      (`chartIdxEquiv`'s `ChartIdx = Σ k, Fin(schurDim) ⊕ Fin(liftDim)` layer) and its OUTPUT grading
>      (`paramsEquivFlat`'s `FlatIdx = Σ (Σ s, Fin M_s), Fin M_{s+1}` layer) are TWO DIFFERENT
>      `Fintype.equivFin` bijections of `Fin N`. `Matrix.BlockTriangular` (v4.29) consumes a SINGLE
>      grading on rows and columns (no asymmetric variant), so block-triangularity of the REAL frame
>      needs `FlatIdx-layer = ChartIdx-layer` as functions — i.e. rebuild one flattening THROUGH an
>      explicit layer-preserving `FlatIdx ≃ ChartIdx`. NOT a free consequence of the banked locality.
>   2. **The per-block-det `hR`/`hB` (the deferred cast-surface b-1).** The only banked route from
>      `fderiv phiFlatLiveR1`'s diagonal blocks to the engine values (`schurFrame_abs_det`,
>      `lduCoreDeriv_abs_det`, `radial_abs_det_minAdm`) goes through the `composeFold` factored-map
>      equality (`phiFlat_hasFDerivAt_of_factored`) — which is route β, DEAD as-banked. The
>      block-triangular route needs the opaque-width `toSquareBlock` reindex (`Fin blockSize ≃ {i // g i =
>      a}`) tying each real diagonal block to its engine differential — the buildspec's "one genuine
>      cast-surface piece."
>   The route-decision (decorrelated Codex, NOW SUPERSEDED — see UPDATE): take the COARSE headline-shaped
>   grading (radial grade `0` + one grade per boundary), keep `interiorDet_headline_of_blockTri` as-is,
>   and add a single `boundary_block_factorises` lemma. The fine role grading (Brick 1) is then optional.
>
>   **UPDATE (commissioned coarse-route leg — the COARSE grading is ALSO BLOCKED).** Verify-first on the
>   coarse route surfaced that the single-grading `BlockTriangular` route fails even at the boundary
>   level: the INPUT partition (`chartIdxEquiv` boundary counts `schurDim+liftDim`) and the OUTPUT
>   partition (`paramsEquivFlat`/`FlatIdx` layer counts `M_s·M_{s+1}`) are GENUINELY DIFFERENT (concrete
>   witness at `(2,2,2)`: `(6,2)` vs `(4,4)`, same total `8`), so no layer-aligned bijection exists and
>   `Matrix.BlockTriangular` (single grading on rows+cols) cannot express the rectangular/staircase block
>   structure. Banked: `RouteMGradingObstruction.flatLayer_ne_chartBoundary_222`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMGradingObstruction.lean`, sorry-free, `[propext]`). See
>   `coarse-route-grading-obstruction.md` for the full finding + the two constructive routes forward
>   (a re-derived nonlinear chain factor / β-rebuild, or a hand-built staircase det) — both genuine new
>   work, not a bounded cast-cleanup.
> - **Status.** sorry-free, clean-three (forced `#print axioms`) — reviewed (fidelity verdict
>   *survived*; two report-only docstring sharpenings applied: the `RouteMLocalityDet` "in one shot"
>   phrasing now states the small `toDual`-transport wrapper to use it WITH the headline; the
>   `FlatIdx ≃ ChartIdx` phrase now notes the raw per-layer sizes differ so the honest common grading is
>   the COARSE boundary-level one).
