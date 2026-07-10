# Statement card — `genm-sjslice`: the `(3,3,3,4)` corank-2 corner-blow-up crux

The FIRST vertical slice of the native `(S,J)` rank-flag resolution. Formalises the single load-bearing
**crux** of the `(3,3,3,4)` corank-2 branch (vslice cert §5): the finiteness of the binding *corner*
local model after the two radial blow-ups. Module `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJSlice334.lean`.
All theorems clean-three `[propext, Classical.choice, Quot.sound]`, 0 `sorry` (force-recompiled
`#print axioms`).

---

> **Claim (width-general two-block corner).** For two radial blow-ups of block dimensions `h₀+1`,
> `h₁+1` (accumulated Jacobian powers `h₀, h₁`; each loss term order 2) sharing the deep factor, the
> binding corner local model `(u₀²·U₀ + u₁²·U₁)^{−c'}` with Jacobian `|u₀|^{h₀}·|u₁|^{h₁}` and residual
> units `U₀,U₁` bounded below by `a>0` on the unit box has finite `∫⁻` for every `c' < (h₀+h₁+2)/2`
> (the branch threshold where the two codimensions ADD).
>
> - **Lean:** `DLNFibre.DLN.RLCT.sjSlice_corner_two_block_lt_top`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJSlice334.lean` @ `e24a0f2d`)
> - **Gloss.** `∀ h₀ h₁ : ℕ, ∀ c' : ℝ≥0, (c':ℝ) < (h₀+h₁+2)/2 → ∀ U₀ U₁ : (Fin 2 → ℝ) → ℝ, ∀ a : ℝ,
>   0 < a → (∀ u ∈ unitBox 2, a ≤ U₀ u) → (∀ u ∈ unitBox 2, a ≤ U₁ u) →
>   ∫⁻ u in unitBox 2, ENNReal.ofReal ((u 0 ^ 2 * U₀ u + u 1 ^ 2 * U₁ u) ^ (−(c':ℝ)) *
>   (|u 0|^h₀ * |u 1|^h₁)) < ⊤`.
> - **Proved.** The `ℝ≥0∞` box integral is finite (`< ⊤`) below the threshold, unconditionally in
>   `(h₀,h₁)`. Proof: weighted AM-GM at the min-cut weights `((h₀+1)/(h₀+h₁+2), (h₁+1)/(h₀+h₁+2))`
>   dominates the loss base below by `|u₀|^{2w₀}|u₁|^{2w₁}`, so the integrand is dominated by the
>   *separated* monomial `|u₀|^{h₀−2w₀c'}|u₁|^{h₁−2w₁c'}`, which is box-integrable iff both axis
>   exponents `> −1` — and at these weights both coincide at the constraint `c' < (h₀+h₁+2)/2`. Lands on
>   the banked `RouteMSJMonomialLower.prod_rpow_lintegral_Ioo_box_lt_top`.
> - **Assumed.** The units `U₀,U₁` are bounded below by `a>0` on the box (`∀ u ∈ unitBox 2, a ≤ Uᵢ u`) —
>   the vslice cert §8 "shared-support closure / relative corank-step invariant" carried as a hypothesis,
>   exactly as the banked terminal endpoint `RouteMSJTerminal.terminal_monomial_mul_unit_lintegral_lt_top`
>   carries its `hunit`. No measurability of `Uᵢ` is needed (domination is monotone).
> - **Cited.** None (S2-free: no `monomial_rlct`, no `cited_aoyagi_dln`). The `rlct = ½·codim` reading
>   stays Cited elsewhere; this proves box-finiteness at the branch threshold only.
> - **Deferred.** The change-of-variables that PRODUCES this corner model from `gammaPeelIntegral`
>   (front-split → pivot-chart → Schur split → depth reduction → the two radial blow-ups; the CoV/
>   resolution-map mountain, recon GAP §1) is NOT done here — the banked pipeline reaches the corner, this
>   closes the corner. Also deferred: discharging the §8 unit-boundedness `a ≤ Uᵢ` from the actual
>   resolved cores (`frobSq(row·A₂)`) — the opaque-width `Case111/Case222` lift.
> - **Structure & ideas observed (pen-and-paper, vslice cert §5 + covdesign cert §2).** The corner binds,
>   NOT a boundary: `{u₀=0}`/`{u₁=0}` in isolation give `4/2` and `3/2`, min `3/2` (the two-matrix
>   min-undershoot); the true zero is the corner `u₀=u₁=0` where the codims ADD (`4+3=7`). The corner
>   blow-up `u₁=u₀τ` accumulates Jacobian `3+2+1=6`, loss order 2, threshold `(6+1)/2 = 7/2`. Analytic
>   realisation: weighted AM-GM at the min-cut direction is the Newton-polygon support function; the
>   *symmetric* weights (basic AM-GM) reproduce the `3/2`-undershoot, so the weighting is load-bearing.
> - **Route (formaliser).** Dominate rather than change variables: `Uᵢ ≥ a > 0` reduces to the pure
>   radial `(u₀²+u₁²)^{−c'}`; weighted AM-GM (fixed min-cut weights, no case split) → separated rpow
>   monomial → banked `prod_rpow_lintegral_Ioo_box_lt_top` (real-exponent open-box product) + the banked
>   `restrict_unitBox_eq_open` boundary bridge. Avoids the explicit blow-up Jacobian (the deferred CoV).
> - **Status.** sorry-free (reviewer fidelity check requested).

> **Corollary (concrete `(3,3,3,4)` crux, and the charge tie).**
>
> - **Lean:** `DLNFibre.DLN.RLCT.sjSlice334_corner_lintegral_lt_top` — the instantiation at `(h₀,h₁)=(3,2)`
>   (block dims 4,3), threshold `7/2`; `sjSlice334_minAdm_eq : minAdm ![3,3,3,4] = 7` (banked
>   `minAdmRec_eq_minAdm` + `decide`); `sjSlice334_corner_lintegral_lt_top_of_lt_half_minAdm` — the same
>   finiteness stated at the charge-tied threshold `c' < ½·minAdm ![3,3,3,4]`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJSlice334.lean` @ `e24a0f2d`).
> - **Proved.** `7/2 = ½·minAdm(3,3,3,4)` exactly; the concrete corner is finite below it — the concrete
>   slice reproduces the pinned exponent bookkeeping (covdesign cert §2: threshold `½·minAdm`, strict
>   below). The general threshold `(h₀+h₁+2)/2 = ½·((h₀+1)+(h₁+1))` = ½·(sum of block dims) faithfully
>   encodes "the codimensions add".
> - **Deferred.** The full `gammaPeelIntegral ![3,3,3,4] … < ⊤` (the leaf `sjJointResolution` at this
>   chain) — the CoV chain feeding the corner is the deferred mountain.
> - **Status.** sorry-free (reviewer fidelity check requested).

---

## hIH finding (recon controller-decision)

**Self-contained.** The crux (and the flag recursion it terminates) does NOT consume the arity-`hIH`
(`∀ M', RouteMBoxThresholdFinite M'`): the corner finiteness terminates over the rank FLAG at the banked
monomial endpoint (`prod_rpow_lintegral_Ioo_box_lt_top`), not by descending to a reduced-arity chain.
Consistent with covdesign cert §2 ("per-stratum arity-clean") and recon option (b). The full assembly of
`gammaPeelIntegral < ⊤` may still keep `hIH` as an unused signature-compatibility hypothesis (as
`sjJointResolution_frontPeel`'s `_hIH` does).
