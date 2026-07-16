# Statement card — R2, the corank-one edge C-shift bound (D)

## Card — the C-shift change-of-variables bound (LANDED, sorry-free, clean-three)

> **Claim.** The C-integral of satred's corank-one edge fragile residual `(of C).mulVec v + β` over the
> pivot box is dominated by the `a`-dimensional scaled radial (`scaledRadialEuclid`), with the
> `|v_{j₀}|^{−a}` single-column Jacobian constant and β-invariance — so the C-shift carries the corank
> charge `ab/2` (`b=1`: `a/2`, exponent `W^{a/2−c'}`) into the arity−1 comparator.
>
> - **Lean** (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJEdgeCShift.lean` @ commit `95fa63aa7`,
>   branch `expedition/genm-tideD-edgecshift`; network-free, on `RouteMSJEdgeScalar` + Mathlib):
>   - `DLNFibre.DLN.RLCT.affineScale_pi_le` — the `a`-dim core atom: for `v₀ ≠ 0`, shift `β : Fin a → ℝ`,
>     `W > 0`,
>     `∫⁻ y in [−1,1]^a, (W + ∑ᵢ(v₀·yᵢ + βᵢ)²)^{−c'} ≤ (|v₀|^a)⁻¹ · ∫⁻ z:Fin a→ℝ, (W + ∑ᵢzᵢ²)^{−c'}`.
>     (box→ℝ^a a-fortiori + `map_addHaar_smul` Jacobian `|v₀|^{−a}` + translation-invariance β-absorption.)
>   - `DLNFibre.DLN.RLCT.radial_pi_eq_euclid` — `∫⁻ z:Fin a→ℝ,(W+∑zᵢ²)^{−c'} = ∫⁻ x:EuclideanSpace ℝ (Fin a),(W+‖x‖²)^{−c'}` (`W>0`; bridges the pi-radial to `scaledRadialEuclid`).
>   - `DLNFibre.DLN.RLCT.edge_C_shift_bound` — the matrix form: for `v : Fin (u+1) → ℝ`, `j₀` with
>     `v j₀ ≠ 0`, `β : Fin a → ℝ`, `W > 0`,
>     `∫⁻ C in [−1,1]^{a×(u+1)}, (W + ∑ᵢ((of C).mulVec v i + βᵢ)²)^{−c'} ≤ ofReal(2^{a·u}·|v j₀|^{−a}) · ∫⁻ x:EuclideanSpace ℝ (Fin a),(W+‖x‖²)^{−c'}`.
>   - `DLNFibre.DLN.RLCT.edge_C_shift_lt_top` — the finiteness corollary (`a < 2c'`): the LHS `< ⊤`
>     (bound × `scaledRadialEuclid_lt_top`). + a non-vacuity `example` (`a=1`, 2 columns, `v=![1,0]`).
> - **Gloss.** `C = of x.2` (a×(u+1) block, box radius 1 from `outerDom`); `v = Q̃ₚ·ω` (fragile direction);
>   `β = σ·Γη` (C-independent shift); `W = frobSq(P·Q̃ₚ) + transverse` (pivot energy, constant over C). The
>   RHS is `scaledRadialEuclid = W^{a/2−c'}·B` (`RouteMSJEdgeScalar`), so R2 exposes the `W^{a/2−c'}`
>   pivot-energy power that the W-integral (W2) feeds to the arity−1 IH. The proof is a single column-peel
>   (peel column `j₀`, `piFinSuccAbove ∘ arrowProdEquivProdArrow`, volume-preserving) reducing to the
>   `a`-dim affine substitution atom; NOT a transversality-everywhere proof (satred de-risk).
> - **Proved.** all four, unconditionally on their stated hypotheses (`v j₀ ≠ 0`, `W > 0`, `a < 2c'`).
> - **Assumed.** none beyond the stated hypotheses.
> - **Cited.** Mathlib only (`map_addHaar_smul`, `lintegral_add_right_eq_self`, `volume_preserving_pi`,
>   `volume_preserving_piFinSuccAbove`, `volume_measurePreserving_arrowProdEquivProdArrow`,
>   `setLIntegral_prod_symm`, `PiLp.volume_preserving_ofLp`, `EuclideanSpace.real_norm_sq_eq`);
>   `RouteMSJEdgeScalar.scaledRadialEuclid_lt_top`.
> - **Deferred.** this is R2 in isolation (fixed `v ≠ 0`). **Scope (satred recalibration):** R2 is the
>   `a < u` SHORTCUT — its exposed `|v j₀|^{−a}` constant integrates over the assembly only when `a < u`
>   (127/286 edge cells). For `a ≥ u` (159/286) the `v→0` locus (`ω ∈ ker Q_p`, positive-codim) makes
>   `∫|v j₀|^{−a} ~ ∫_{ℝ^u}‖x‖^{−a}` DIVERGE, and the reduced chain does NOT dispose it — so R2-alone is
>   lossy there. The assembly's UNIFORM closer is the `u=rs` route (P2), which handles all `v` without
>   `‖v‖^{−a}`. The full `edge_coupledBox_lt_top` (P2 uniform closer + L3 δ-fold + W2 IH + R3 + the wiring)
>   remains — see thread.md.
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]` (all four, force-recompiled
>   `#print axioms`).
