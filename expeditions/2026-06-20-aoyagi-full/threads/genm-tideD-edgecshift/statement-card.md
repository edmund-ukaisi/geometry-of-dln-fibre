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
>   - `DLNFibre.DLN.RLCT.edge_leaf_gamma_bound` — R2 composed with the free Γ-direction (P1) integral:
>     `∫_{γ∈[−1,1]^a}∫_{C∈[−1,1]^{a×(u+1)}}(W+‖(of C)·v + d•γ‖²)^{−c'} ≤ 2^a·2^{a·u}·|v j₀|^{−a}·scaledRadialEuclid(W,c')`.
>     The free direction adds only a finite `2^a` volume factor (R2 β-invariance); δ-free clean. The a<u
>     clean-leaf composition (verified GO by satred).
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
> - **Deferred / scope (satred, VERIFIED — definitive after churn).** R2 + `edge_leaf_gamma_bound` are
>   CORRECT bricks giving the full `ab/2` corank charge (`W^{a/2−c'}`), β-invariant, σ-independent, δ-free
>   in the open edge window `c' > (M₀−u)(M₁−u)/2`. The edge splits by `a` vs `u` (`a = M₀−u`, `u+1` = pivot
>   columns):
>   - **`a < u`: CLEAN network-free leaf, fully GO** with what's here. Close = `edge_leaf_gamma_bound`
>     (landed) → `|v_{j₀}|^{−a}`-disposal over the reduced params (finite iff `a<u`: `v=Q̃ₚ·ω`, `Q̃ₚ` has
>     a kernel, `‖v‖ ~ dist` to a codim-`u` locus ⟹ `∫_ω‖v‖^{−a}<⊤ ⟺ a<u`, = `corner_block_lintegral_lt_top`
>     with `g=‖·‖²`, `c'=a/2`, `N=u`) → arity−1 IH on `redChain u M` (strict range via `sjChargeBudget_le`).
>     δ-fold only at the single exponent `c'=ab/2` (a bounded/cutoff-radial matter in the W2 step).
>   - **`a ≥ u`: ENTANGLED — satred's design pass.** R2's dropped-transverse bound is too lossy;
>     the transverse `‖C·Q̃ₚ·Π_⊥ω‖²` must be KEPT (supplies extra C-directions taming `‖v‖^{−a}`).
>     satred consolidating the DEFINITIVE reduction (a<u leaf + a≥u fuller) into the D-cert as single
>     source of truth.
> - **Precision (reviewer + Codex, corrects an earlier gloss).** The FULL-SPACE `scaledRadialEuclid`
>   `= W^{a/2−c'}·B` DIVERGES at `c' = a/2` (`B = ∫_{ℝ^a}(1+‖s‖²)^{−c'} = +∞` for `a = 2c'`) — it does NOT
>   `≍ log(1/W)`. The corank-one tie-log is a property of the BOUNDED/cutoff radial, not this full-space
>   comparator; the open edge window `c' > a/2` excludes the critical exponent, so `edge_leaf_gamma_bound`
>   gives a finite RHS throughout.
> - The corner is finite, RLCT `= ½minAdm(M)`, NO wall (satred, reliable). The full `edge_coupledBox_lt_top`
>   (a<u disposal wiring + a≥u fuller lemma + W2 IH + R3 + the assembly wiring) remains — see thread.md.
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]` (all four, force-recompiled
>   `#print axioms`).
