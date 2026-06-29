# Statement card — b-FrameM-1a: the outer reshape Q_M + |det Q_M|=1, `genm-detcomp`

> **Claim (b-FrameM-1a).** The outer coordinate-reshape `Q_M = paramsEquivFlat ∘ pack_M` (the
> aligned-basis bridge of the (A') `Frame_M` route) is a measure-preserving continuous linear equiv with
> `|det Q_M| = 1`. The clean factorization `phiFlatLiveR1 = Q_M ∘ T_M` is then DEFINITIONAL (no refuted
> map-equality), giving `|det Dφ| = |det DT_M|`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.{QMcle, QMcle_abs_det}` (+ `flatEquivOfLinear`, `flatEquivOfLinear_coe`,
>   `QMcle_coe`) (`lean/DLNFibre/DLN/RLCT/Validate/RouteMFrameQM.lean` @ `<pending — off genm-detcomp e5451764>`)
> - **Gloss.** For any slot bijection `e : Fin (routeMAmbient M) ≃ FlatIdx M`:
>   `QMcle M e : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)` is `paramsEquivFlat M ∘ (flatEquivOf M e).symm`
>   (`QMcle_coe`), and `|det (QMcle M e)| = 1` (`QMcle_abs_det`).
> - **Proved (unconditional, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`):** all.
>   `Q_M` measure-preserving (`flatEquivOf` MP `.symm` ∘ `paramsEquivFlat` MP), so `|det| = 1` via the
>   banked `continuousLinearMap_abs_det_eq_one_of_measurePreserving`. `flatEquivOfLinear` is the ℝ-linear
>   mirror of the measurable `flatEquivOf` (`LinearEquiv.piCurry` + `funCongrLeft e`; same coe, `funext;rfl`).
> - **Reused (banked):** `ParamsReshapeMP` (`flatEquivOf`, `measurePreserving_flatEquivOf`,
>   `continuousLinearMap_abs_det_eq_one_of_measurePreserving`), `ParamsFlatLinear` (`paramsEquivFlatLinear`,
>   `paramsEquivFlatLinear_coe`). The (1,2,1)/(3,3,3,3) `Q121`/`Q3333` outer-reshape, generalized to
>   arbitrary M + arbitrary slot bijection `e`.
> - **Assumed.** none (works for ANY `e`; the role-ALIGNED `e` choice is deferred to 1c/1d where the
>   grading needs it — `Q_M`'s `|det|=1` holds regardless of `e`).
> - **Cited.** none.
> - **Deferred (the rest of (A')):** 1b `Kparam_M` (the LDU lens making role-blocks square — the
>   count-alignment crux; |det| = banked `lduCoreDeriv_abs_det`); 1c `T_M = pack_M.symm ∘ chartParamsGen`
>   + `DT_M` HasFDerivAt (reuse b-FrameM-2 atoms) + the role-grading `frameB_M`; 1d block-tri (reuse
>   `toMatrix_blockTriangular_of_locality` + live-locality 1a) + per-role-block dets (engine) → assemble
>   via `interiorDet_headline_of_blockTri`. Then `|det Dφ| = |det Q_M|·|det DT_M| = 1·headline`.
> - **Status.** sorry-free, axiom-clean (forced `#print axioms`) — awaiting reviewer.
