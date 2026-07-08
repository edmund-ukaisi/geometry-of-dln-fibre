# Statement card — `genm-sjnative` decorated peel-charge soundness

> **Claim.** One decorated R-BLOWUP peel at a legal cut `u ≤ min(M₀,M₁)` is threshold-monotone: the
> parent chain's minimal admissible codim is dominated by the emitted Case-2 block charge `(M₀−u)(M₁−u)`
> plus the reduced chain's minimal admissible codim — `minAdm M ≤ (M₀−u)(M₁−u) + minAdm(redChain u M)`.
> The exponent-shift form and the binding-cut equality (non-vacuity) accompany it.
>
> - **Lean:** `DLNFibre.DLN.RLCT.minAdm_le_peelCharge_add_redChain`,
>   `half_minAdm_sub_half_peelCharge_le`, `exists_binding_cut`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDecoratedCharge.lean` @ `fd120b0b`)
> - **Gloss.** For a `≥3`-width chain `M : Fin (L+3) → ℕ` and `u ≤ min(M 0)(M 1)`:
>   `minAdm M ≤ peelCharge M u + minAdm (redChain u M)` where `peelCharge M u = (M 0 − u)*(M 1 − u)`;
>   the ℝ form `(minAdm M)/2 − (peelCharge M u)/2 ≤ (minAdm (redChain u M))/2`; and there EXISTS a cut
>   `u ≤ min(M 0)(M 1)` making the first an equality.
> - **Proved.** All three, unconditionally, sorry-free. Immediate from the banked value-fold
>   `LayerSplit_value_eq_minAdm` (the peel value is a member of the `inf'` equal to `minAdm M`) +
>   `Finset.inf'_le` / `Finset.exists_mem_eq_inf'`. Axiom-clean `[propext, Classical.choice, Quot.sound]`
>   (forced `#print axioms`, no `sorryAx` / `monomial_rlct` / `cited_aoyagi_dln`).
> - **Assumed.** `u ≤ min(M 0)(M 1)` (cut legality) — the same admissibility the informal peel carries.
> - **Cited.** none.
> - **Deferred.** This is the COMBINATORIAL soundness (`carrierThreshold_mono`, cert DATA-C `0/171`) of
>   `decorated_peel_step` ONLY. The analytic peel it gates — the radial Morse charge + the
>   measure-preserving change of variables removing the `Δ ↦ Δ·Q_b` anisotropy (the cert's ~65–75%
>   genuinely-new construction) — is NOT here. The decorated predicate `DecoratedBoxThresholdFinite`, the
>   carrier `PartialProfile`/`SJDecoration`, `decorated_base`, the `π=∅` consumer
>   `routeMBoxThresholdFinite_of_decorated`, and the discharge of `sjJointResolution` remain the mountain
>   (see the thread report). `sjJointResolution` is UNTOUCHED (per mandate).
> - **Route.** Native decorated R-BLOWUP (cert `genm-r1decorated`, BUILD adjudication). This brick reuses
>   the banked layer-peel value-fold; it is the threshold-monotone gate of the exponent-shift the peel
>   hands to the strong IH at the reduced chain.
> - **Status.** sorry-free (awaiting reviewer fidelity check).
