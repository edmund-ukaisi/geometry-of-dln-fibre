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
> - **Deferred.** this is R2 in isolation (fixed `v ≠ 0`). The `{v=0}` sub-locus is NOT an R2 case — the
>   assembly disposes it via the reduced chain (satred). The OUTER integrability of the `|v j₀|^{−a}`
>   constant over the reduced params (edgebrick: adaptive-pivot `j₀ = argmax|vⱼ|`, `a ≤ codim{v=0}`) is an
>   assembly-level (P2/L3/W2) obligation, not R2. The full `edge_coupledBox_lt_top` remains (see thread.md).
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]` (all four, force-recompiled
>   `#print axioms`).
