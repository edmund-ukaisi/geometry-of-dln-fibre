# Statement card — #82 FOLD2: `deepestEPivot_deriv` (the shear-CLE derivative)

> **Claim.** `deepestEPivot`'s strict derivative at `0` is bundled with an invertible CLE `e` equal to
> the total straightening CLM — the `#120`-corrected shear (NOT `fst`). The `_deriv` ASSEMBLY is complete;
> it reduces to ONE isolated analytic lemma.
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepestEPivot_deriv`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean` @ `d9c74e1`).
>
> - **Statement.**
>   `∃ (D_E : (Reg × Gauge) →L[ℝ] Reg) (e : DeepestSplit ≃L[ℝ] DeepestSplit),`
>   `HasStrictFDerivAt deepestEPivot D_E 0 ∧ (e : →L) = regStraightenTotalCLM D_E`
>   (`Reg = Fin (deepestNReg H r) → ℝ`, `Gauge = Fin (deepestNGauge H r) → ℝ`).
>
> - **Proved (the ASSEMBLY, sorry-free around the one obligation; the surrounding infra clean-three).**
>   The packaging closes (Codex `fold2-deriv-route` Route B):
>   - `D_E := fderiv ℝ deepestEPivot 0`, `hsd : HasStrictFDerivAt deepestEPivot D_E 0` via
>     `(deepestEPivot_contdiff).hasStrictFDerivAt` (free from `_contdiff`).
>   - reg-block `= D_E.comp regInCLM` via the chain rule (`hsd.comp (x:=0) hregIn`, `regInCLM = (id).prod 0`
>     the reg-slice embedding `r ↦ (r, 0)`).
>   - that reg-block `= id` by `deepestEPivot_regSlice_fderiv_id` (the ONE obligation, see below).
>   - `regStraightenTotalCLM_equiv_of_regBlock_id D_E hblock` packages the invertible shear `e`
>     (`id + N`, `N²=0`, `clmShearEquiv`).
>
> - **Banked infrastructure (sorry-free, clean-three).**
>   - `hasStrictFDerivAt_prodAux_entry` / `hasStrictFDerivAt_prod_entry`
>     (`DeepestFramedProduct.lean`) — the entry-wise strict derivative of the L-fold matrix product
>     (`HasStrictFDerivAt.fun_sum` of `.mul`, cast-layer via the `eq_mpr_eq_cast/cast_eq` idiom). Did NOT
>     exist in DLNFibre before; the reusable product-derivative machine.
>   - `regStraightenTotalCLM_equiv_of_regBlock_id` + `regInCLM`
>     (`DeepestRegAbsorbIFT.lean`) — the GENERIC shear-CLE: `D_E(r,0)=r` ⟹ the total CLM is the
>     invertible `id+N` (decouples invertibility from the analytic content).
>
> - **The SINGLE remaining obligation (the analytic crux, a clean dispatch target).**
>   `deepestEPivot_regSlice_fderiv_id :`
>   `HasStrictFDerivAt (fun r0 : Reg => deepestEPivot H r hr hL (r0, 0)) (ContinuousLinearMap.id ℝ Reg) 0`
>   — the gauge-zero reg-slice derivative is the identity. THE #91/g239 idempotent-sandwich:
>   `dP|_0 = Σ_s corner·δC_s·corner` (corners idempotent, `prodAux_framedParamsReg_zero` banked) keeps,
>   on the reg-residual blocks, only the `(0,0)` X-pivot — which equals the reg-input on the pivot coords.
>   - **Cert:** `origin/g213-pin1-de0` (general-L `dE(0) = (Σ_s X_s, Y_L, Z_1)`, 40-config sweep) +
>     `origin/g239-de-encoding` (the `D_E = pack ∘ sandwich ∘ slotRead` transcription).
>   - **Named wall (Codex + g239):** the opaque `regResidualPack` / `regGaugeSlotEquiv` packing — the
>     reg-coords are an abstract `Fintype.equivFin` bijection, NOT syntactically `(X_first, Y_last, Z_first)`.
>     The proof must thread the product-derivative through this packing to show the net map is `id`.
>   - **Routing:** flagged to the controller for a product-derivative cert (pp2 / fresh isolated
>     formaliser) — the from-scratch product-derivative-through-opaque-packing. Wires in instantly on
>     landing (the `_deriv` assembly is closed around it).
>
> - **Consult artefact:** `codex/fold2-deriv-route-{prompt,answer}.md`.
