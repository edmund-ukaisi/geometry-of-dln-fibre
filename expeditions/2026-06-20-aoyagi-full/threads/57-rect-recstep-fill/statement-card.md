# Statement card — RECTANGULAR `L=2` Schur per-step (the general-`(M0,M1,M2)` UPPER leg)

> **Claim.** The deferred rectangular per-step `RectSchurRecStep p (rectSchurLambda p)` — the asymmetric
> (`M0 ≠ M1`, `Δ : Fin m → Fin n` RECTANGULAR) generalisation of the proven square `schurRecStep_p` — holds
> for ALL `(m, n, p)`, sorry-free. It is the SOLE remaining input to the general-`L=2` finiteness
> `routeMBoxThresholdFinite_mnp` + the `cover_le` UPPER leg `routeMLayerCover_coverLe_mnp`, closing the
> general-`(M0,M1,M2)` UPPER leg (regime ii of the aoyagi-full expedition).
>
> - **Lean:** `DLNFibre.DLN.RLCT.rectSchurRecStep_mnp`,
>   `DLNFibre.DLN.RLCT.routeMBoxThresholdFinite_mnp`, `DLNFibre.DLN.RLCT.routeMLayerCover_coverLe_mnp`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurRectCapB.lean`).
> - **Gloss.** `rectSchurRecStep_mnp`: given the threshold contract `RectSchurThreshold p (rectSchurLambda p)`
>   and the joint lower IH `RectSchurLowerIH p (rectSchurLambda p) m n`, for `0 < c' < rectSchurLambda p m n`
>   the rectangular free-box core `RectSchurCore m n p c' T = ∫_{Δ∈matBox m n T}∫_{S∈matBox n p T}
>   frobSq(Δ·S)^{−c'} < ⊤`. The threshold `rectSchurLambda p m n = ½·minAdm(![m,n,p]) =
>   ½·inf_{0≤t≤min(m,n)}[(m−t)(n−t)+tp]`. Dispatches on the recursion measure `min(m,n)`. The two deliverables
>   then assemble the general-`(m,n,p)` `hbox` + `cover_le` (the asymmetric analogs of
>   `routeMBoxThresholdFinite_rrp` / `routeMLayerCover_coverLe_rrp`).
> - **Proved.** All three sorry-free. `rectSchurRecStep_mnp` and `routeMBoxThresholdFinite_mnp` carry exactly
>   `[propext, Classical.choice, Quot.sound]` (clean-three). `routeMLayerCover_coverLe_mnp` carries
>   clean-three + `monomial_rlct` (the SAME S2 axiom the square headline already rides, entering only the
>   `hfin` leaf-sum side via `routeMLayerCover_hfin` — no new axiom). No `sorry` / `native_decide` / `#exit`.
> - **The dispatch (on `min(m,n)`, asymmetric analog of the square `match r`).**
>   - `min(m,n) = 0` — vacuous (`rectSchurLambda = 0` via the threshold's `lambda0_*`, contradicts `0 < c'`).
>   - `min(m,n) = 1` — the corank-1 leaf `schurCoreRect_one`. Here `rectSchurLambda = ½·min(n,p)` (resp.
>     `½·min(m,p)`) `≤ p/2` (the `t=1` stratum is `(m−1)(n−1)+p = p`, one factor vanishes —
>     `minAdm_mnp_le_p_of_min_one`) AND `≤ mn/2` (`rectSchurLambda_le_mul`), so BOTH cap-B caps hold and the
>     directMorse cover fires. NO separate separable form (unlike the square `schurCoreP_one`); it is the same
>     cap-B machinery — cleaner than the square case.
>   - `min(m,n) ≥ 2` — split on `le_or_gt (rectSchurLambda p m n) (p/2)`:
>     * **cap-B** (`≤ p/2`): `schurCoreRect_directMorse`, the binding stratum `t = 0`. The `mn`-chart
>       radial-`Δ` cover (`matBoxRect_outer_flat` + `gFlatRect_cover_sum`) → per-chart = radial a-axis divisor
>       `|y|^{mn−1−2c'}` (`radial_aAxis_divisor_rect`, `c' < mn/2`) × the cap-B angular residual
>       `schurRatioResidRect_capB_lt_top` (`c' < p/2`, KEEPS the Schur residual, closed by the abstract-`Z`
>       Morse dominator `radial_morse_dominates_absZ_le`). NO recursion.
>     * **cap-A interior** (`> p/2`): the recursion-driven carve `schurCoreRect_capA_interior` (item 3, the
>       `M22 ↦ Sc` translation-domination + the lower IH `hIH`).
> - **Reused / asymmetric.** Built on the pinned rectangular interface (`RmatRectNorm`, `innerSRect_eq_norm`,
>   `schur_minorPivot_split_rect` at `t = 1`, `frobSqTopRowRect_eq_shear`, `stepShearRect`) + the radial half
>   from `RouteMSchurRectStep` (`chart_integrand_factorRect`, `flatBoxRect_blowup_mem_iff`,
>   `radial_aAxis_divisor_rect`, `pivotBlowupOnDeriv_det_rect`) + the abstract-`Z` Morse dominator
>   (`radial_morse_dominates_absZ_le`, `Kbound`). The residual is `(m−1)×(n−1)` (NOT square `(r−1)²`); the
>   Morse-dominator `Z`-box is `(n−1)×p` (contracted dim `n`); the per-`R` bound is `R`-uniform.
> - **Cited.** none new (network-free real analysis; reuses the banked engine + the rectangular interface).
> - **Architecture note.** `rectSchurRecStep_mnp` lives in `RouteMSchurRectCapB`, NOT in the SPEC file
>   `RouteMSchurRect`, because its proof imports the carve / cover stack which in turn imports the SPEC — a
>   forward-fill of the SPEC's `sorry` stub is impossible. The SPEC's stub `rectSchurRecStep_stub` + the two
>   gated deliverables were RELOCATED downstream (the same split the square family uses:
>   `routeMBoxThresholdFinite_rrp` lives in `RouteMBoxThresholdRRP`, not in `RouteMSchurGeneral`). The SPEC
>   file stays sorry-free: predicates, the WellFounded-on-`min(m,n)` wrapper `rectCore_schurGen_lt_top`, the
>   threshold arithmetic + witness, and the layer reshape.
> - **Validation.** Asymmetric anchor `(2,3,4)` (`minAdm = 6`, threshold `3`) ≠ square `(2,2,4)`
>   (`minAdm = 4`) `#eval`-pinned — the square `SchurCore` does NOT reach the larger asymmetric threshold,
>   so the rectangular core is genuinely new content, not a re-statement. Full aggregator `lake build
>   DLNFibre` green; forced `#print axioms` confirms the footprint (build exit-0 alone can mask `sorryAx`).
> - **Status.** sorry-free (awaiting reviewer fidelity check + controller cone-merge into canonical).
