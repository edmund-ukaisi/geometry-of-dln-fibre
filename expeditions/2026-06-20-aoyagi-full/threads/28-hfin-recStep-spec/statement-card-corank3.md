# Statement card — `core_schur3_lt_top` (corank-3 core finiteness, the recursion's first firing)

> **Claim.** The corank-3 determinantal-core integral is finite below the JOINT-core SUM threshold
> `λ_{3,4} = 4`: for `0 < c' < 4`, over the unit boxes,
> `∫_{Δ∈[−1,1]^{3×3}} ∫_{S∈[−1,1]^{3×4}} ‖Δ·S‖_F^{−2}^{… as ^{−c'}} < ∞`. The threshold `4 = jp/2 + λ_{2,4}
> = 2 + 2` is the JOINT-core SUM (NOT the corank-2 `2`) — the recursion's first real firing, where the
> residual Schur complement is a `2×2` block, not a scalar.
>
> - **Lean:** `DLNFibre.DLN.RLCT.core_schur3_lt_top`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCorank3.lean` @ `1b0526d0`)
> - **Gloss.** For `c' : ℝ`, `0 < c'`, `c' < 4`:
>   `∫⁻ Δ in matBox 3 3 1, ∫⁻ S in matBox 3 4 1, ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c')) < ⊤`,
>   where `matBox r n 1 = [−1,1]^{r×n}`, `rmatMul` is the raw matrix product, `frobSq` the squared
>   Frobenius norm `∑ᵢⱼ (·)ᵢⱼ²`.
> - **Proved.** The finiteness, unconditionally, for every `0 < c' < 4`, at the **unit box** (radius 1).
>   Route: `Δ`-outer reindex to the `Fin 9` flat carrier (`matBox3_outer_flat`); `recStep` 9-chart
>   max-modulus-entry cover (`gFlat3_cover_sum`); per-chart finiteness (`matBox3_chart_lt_top`): radial CoV
>   (Jacobian `|y_p|⁸`) + Tonelli factoring the radial axis (`radial_aAxis_divisor_lt_top 3`, `c' < 9/2`)
>   from the angular ratios; the inner JOINT ratio-residual (`schurInner3_ratiofin`) closed by the `(3,3,4)`
>   anchor's `ratioResidual_lt_top` (defeq: `innerS3 c' 1 = angA1Int`, `Rmat3 = Rmat334`); `c' ≤ 2` by the
>   exponent-bump `x^{−c'} ≤ 1 + x^{−3}` to the `c'' = 3 ∈ (2,4)` case; `ENNReal.sum_lt_top` over 9 charts.
> - **Assumed.** None (no open hypothesis beyond `0 < c' < 4`).
> - **Cited.** None new. Reuses the BANKED, sorry-free `(3,3,4)` anchor (`RouteM334Ratiofin.ratioResidual_lt_top`
>   and its `resolved334_box_lt_top`/`zE`/`bgShift` JOINT recognition) and the corank-2 depth-2 weld
>   (`RouteMSchurDepth2.core_schur2_lt_top`).
> - **Deferred (named).** **General box radius `T`.** The statement is at the **unit box** (`T = 1`, the
>   operative `routeMBaseNbhd = (−1,1)` radius), NOT general `T` (the corank-2 `core_schur2_lt_top` is
>   general-`T`). General-`T` `= T^{21−4c'}·(T=1)` by box-scaling, which needs a matrix-space
>   `lintegral_comp_smul` (absent in Mathlib v4.29; buildable from
>   `Real.map_linearMap_volume_pi_eq_smul_volume_pi`) OR radius-`T` versions of the `(3,3,4)` `Jint`/`Ginner`
>   route. Self-contained general-`K` N2b-route bricks (`resolvedShiftR2c3_le`, `schurResid2_translate_le`,
>   `frobSqShiftR2c3_ne_zero_ae`, `core_T_peel_le_ae_c3`) are banked sorry-free as the alternative carrier
>   but are NOT on this `T = 1` live path. **The arbitrary-depth WellFounded-on-corank recursion** (the next
>   milestone) is also out of scope here.
> - **Route.** Controller-relayed brief (the per-chart assembly wiring) + the reuse insight discovered
>   in-thread: the genuinely-new JOINT recognition was already banked by the `(3,3,4)` anchor, so the inner
>   heart is a 1-line reuse rather than a re-derivation via N2b.
> - **Status.** sorry-free; `#print axioms = [propext, Classical.choice, Quot.sound]` (forced, olean-fresh).
>   Awaiting reviewer fidelity check.
