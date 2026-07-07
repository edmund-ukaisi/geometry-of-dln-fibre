# Statement card — `genm-sjpeel-blow` (R1-UPPER `(S,J)` boundary-peel blow-up tide)

## Card 1 — the corank-block residual-power atom (LANDED, sorry-free)

> **Claim.** For a `p × q` matrix block `D` (`p, q ≥ 1`) on a strictly-positive core `w > 0`, with
> `c'` above the block Morse threshold `pq/2`, the box integral carries a residual power of the core:
> `∫_{[−T,T]^{p×q}} (frobSq D + w)^{−c'} dD ≤ Cresid(p·q) c' · w^{−(c' − pq/2)}`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.matBox_corank_residual_le`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorankResidual.lean` @ `a819d55c`)
> - **Gloss.** The `pq`-dimensional block `D`, integrated over the cube `matBox p q T`, peels at
>   threshold `pq/2` and leaves the positive core `w` at the SHIFTED exponent `c'' = c' − pq/2`,
>   times a `w`-independent finite constant `Cresid(pq) c' = ∫_{ℝ^{pq}}(‖·‖²+1)^{−c'} < ∞`. This is
>   Aoyagi's per-step exponent shift `c' ↦ c' − ½·a` at block dimension `a = pq = (M₀−t)(M₁−t) =`
>   `peelExp M t`, for the corank (Schur-complement) block `Γ`.
> - **Proved.** The full inequality, unconditionally, for all `p,q ≥ 1`, `T > 0`, `w > 0`,
>   `c' > pq/2`. Reduction: the `p×q → Fin(p·q)` measure-preserving flatten `eMatFlat` (the `e22`
>   generalisation: `piCurry` ∘ `arrowCongr'`), sending `frobSq D = ∑ₖ (eMatFlat D k)²` and
>   `matBox p q T ↔ morseBox (p·q) T`, then the banked `radial_morse_residual_power_le`.
> - **Assumed.** `w > 0` (the core is strictly positive) and `c' > pq/2` (above the block threshold);
>   both are genuine (`w = 0` is the null locus handled elsewhere; `c' ≤ pq/2` makes the block itself
>   non-integrable).
> - **Cited.** none beyond the banked `RadialResidualPower` (whose only analytic input is Mathlib's
>   Japanese-bracket `integrable_rpow_neg_one_add_norm_sq`). S2-FREE.
> - **Deferred.** The **anisotropic** corank form `∫ (g² + frobSq(Γ·Q_bot))^{−c'} dΓ` (Γ coupling to
>   the tail bottom-rows `Q_bot`) — this atom is the isotropic special case `Q_bot = isometry`;
>   recovering the anisotropic form is a linear c.o.v. `Γ ↦ Γ·Q_bot` whose Jacobian is the coupling
>   factor, the (S,J)-resolution content.
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]` (forced
>   `#print axioms`). Not yet reviewer-confirmed for fidelity.

## Finding — the pointwise `lintegral_mono_ae` route for `sjBoundaryPeel` is UNSOUND

The first design sketch discharges `sjBoundaryPeel` by a POINTWISE-in-`A'` inner-fibre bound
`∫_{A₀∈box} frobSq(A₀·Q)^{−c'} ≤ C · ∑_t P_tail_t(Q)^{−(c'−a/2)}·P_full(Q)^{−a/2}` (`Q = prod(tail) A'`)
then `lintegral_mono_ae`. **This pointwise bound is false** for `c' ≥ M₀/2` on (and near) the
rank-deficient-`Q` locus:

- For rank-deficient `Q`, `A₀·Q = 0` on the codim-`(M₀·rank Q)` locus `{A₀ : rows ⊥ colspace Q}`, and
  `∫_{A₀} frobSq(A₀·Q)^{−c'}` **diverges** once `2c' ≥ M₀` (the pivot-column integral
  `∫‖A₀·u‖^{−2c'}` over the rank direction `u` is non-integrable). The RHS stays finite, so the ratio
  `F/RHS → ∞` approaching the rank-deficient locus — **no uniform `C`** (verified `r1u_pointwise_stress.py`:
  ratios `5·10⁵`, `3.7·10⁸` near threshold; analytic `r1u_diverge.py`).
- The `{P_tail = 0}` null-locus collapse (`Real.rpow 0^{neg}=0`) flagged in `sjBoundaryPeel`'s docstring
  is a SUBSET of the failure; the real obstruction is the whole rank-deficient neighbourhood, which is
  NOT null. Decorrelated Codex xhigh independently gave the same verdict + a `p=1,q=2` counterexample
  (`codex/brick-answer.md`).

**Consequence.** `sjBoundaryPeel` (which IS true) must be proved by the per-pivot-chart radial blow-up
**integrated over each chart** (coupling `A₀` and `A'`) — Aoyagi's `(S,J)` resolution — NOT by
`lintegral_mono_ae` on a pointwise bound. This atom (`matBox_corank_residual_le`) is the isotropic
corank-block step that per-chart route consumes after the anisotropy is removed. `sjBoundaryPeel` was
left as its honest sorry (not laundered).
