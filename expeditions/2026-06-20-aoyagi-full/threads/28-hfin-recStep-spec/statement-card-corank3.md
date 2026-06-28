# Statement card — `core_schur3_lt_top` (corank-3 core finiteness, the recursion's first firing)

> **Claim.** The corank-3 determinantal-core integral is finite below the JOINT-core SUM threshold
> `λ_{3,4} = 4`: for `0 < c' < 4` and EVERY box radius `T > 0`,
> `∫_{Δ∈[−T,T]^{3×3}} ∫_{S∈[−T,T]^{3×4}} ‖Δ·S‖_F^{−2c'} < ∞`. The threshold `4 = jp/2 + λ_{2,4} = 2 + 2`
> is the JOINT-core SUM (NOT the corank-2 `2`) — the recursion's first real firing, where the residual
> Schur complement is a `2×2` block, not a scalar.
>
> - **Lean:** `DLNFibre.DLN.RLCT.core_schur3_lt_top` (general-`T`); `…_unitBox` (the `T = 1` base)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCorank3.lean` @ `<commit-sha>`)
> - **Gloss.** For `c' : ℝ`, `0 < c'`, `c' < 4`, `T : ℝ`, `0 < T`:
>   `∫⁻ Δ in matBox 3 3 T, ∫⁻ S in matBox 3 4 T, ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c')) < ⊤`,
>   where `matBox r n T = [−T,T]^{r×n}`, `rmatMul` is the raw matrix product, `frobSq` the squared
>   Frobenius norm `∑ᵢⱼ (·)ᵢⱼ²`.
> - **Proved.** The finiteness, unconditionally, for every `0 < c' < 4` and every `T > 0`.
>   - **`core_schur3_lt_top_unitBox`** (`T = 1`): `Δ`-outer reindex to the `Fin 9` flat carrier
>     (`matBox3_outer_flat`); `recStep` 9-chart max-modulus-entry cover (`gFlat3_cover_sum`); per-chart
>     finiteness (`matBox3_chart_lt_top`): radial CoV (Jacobian `|y_p|⁸`) + Tonelli factoring the radial axis
>     (`radial_aAxis_divisor_lt_top 3`, `c' < 9/2`) from the angular ratios; the inner JOINT ratio-residual
>     (`schurInner3_ratiofin`) closed by the `(3,3,4)` anchor's `ratioResidual_lt_top` (defeq:
>     `innerS3 c' 1 = angA1Int`, `Rmat3 = Rmat334`); `c' ≤ 2` by the exponent-bump `x^{−c'} ≤ 1 + x^{−3}`.
>   - **general `T`**: `= ofReal(T^{21−4c'}) · (unit box)` via the box-scaling primitive
>     `lintegral_matBox_smul` (radius CoV on both the `Δ`- and `S`-boxes, Jacobian `T^9·T^{12}`) + the
>     degree-4 core homogeneity `frobSq_rmatMul_smul_both` (`frobSq((T•Δ)·(T•S)) = T⁴·frobSq(Δ·S)`); the
>     finite radius factor `T^{21−4c'}` transfers finiteness from the unit box.
> - **Assumed.** None (no open hypothesis beyond `0 < c' < 4`, `0 < T`).
> - **Cited.** None new. Reuses the BANKED, sorry-free `(3,3,4)` anchor
>   (`RouteM334Ratiofin.ratioResidual_lt_top` and its `resolved334_box_lt_top`/`zE`/`bgShift` JOINT
>   recognition); the corank-2 depth-2 weld (`RouteMSchurDepth2.core_schur2_lt_top`); and the Mathlib
>   `Measure.map_addHaar_smul` (the addHaar dilation scaling, for the box-scaling primitive).
> - **Deferred (named).** **None for the `(3,3,4)` corank-3 instance.** The general-`T` caveat is now
>   CLOSED (the scaling primitive `lintegral_matBox_smul` was built — a reusable matrix-space radius-CoV).
>   **The arbitrary-depth WellFounded-on-corank recursion** (the next milestone, owned by genm-recstep) is
>   out of scope here but CONSUMES this `core_schur3_lt_top` + the bricks (`resolvedShiftR2c3_le`,
>   `schurResid2_translate_le`, `lintegral_matBox_smul`).
> - **New reusable infrastructure (banked sorry-free).** `lintegral_matBox_smul` (matrix-box radius-CoV:
>   `∫_{matBox r n T} g = ofReal(T^{r·n})·∫_{matBox r n 1} g(T•·)`), `smul_mem_matBox_iff`,
>   `frobSq_rmatMul_smul_both` (degree-4 homogeneity), + the general-`K` N2b-route bricks
>   (`schurResid2_translate_le`, `resolvedShiftR2c3_le`, `frobSqShiftR2c3_ne_zero_ae`, `core_T_peel_le_ae_c3`).
> - **Route.** Controller-relayed brief (per-chart assembly wiring → unit box; then general-`T` lift via a
>   reusable scaling primitive) + the reuse insight discovered in-thread (the JOINT recognition was already
>   banked by the `(3,3,4)` anchor, so the inner heart is a 1-line reuse).
> - **Status.** sorry-free + **reviewed** (PASS on the unit-box base, 2026-06-28). `#print axioms = [propext,
>   Classical.choice, Quot.sound]` for both `core_schur3_lt_top` (general-`T`) and `lintegral_matBox_smul`
>   (forced, olean-fresh). The general-`T` lift re-derives from the reviewed unit-box base + the axiom-clean
>   scaling primitive; a re-review of the general-`T` wrapper + the scaling primitive is appropriate.
