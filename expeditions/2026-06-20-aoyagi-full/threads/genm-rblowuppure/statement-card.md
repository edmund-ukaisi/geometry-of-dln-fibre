# Statement card — `genm-rblowuppure` (PURE R-BLOWUP joint corank-block Morse peel)

Tide: `genm-rblowuppure` (R1-UPPER degenerate-strata finiteness via the PURE `(S,J)` radial recursion,
NOT the atom). Branch `genm-rblowuppure`, off `origin/genm-rblowup2` @9818b832.

---

> **Claim.** For a `p × q` corank block `Δ` (`p, q ≥ 1`) coupled to an arbitrary outer parameter
> `z ∈ Z` (finite outer volume `μ Z < ∞`) through a NON-NEGATIVE additive core `W z ≥ 0`, the
> **joint** integral of the isotropic loss `(frobSq Δ + W z)^{−c'}` over `matBox p q T × Z` is finite
> below the block Morse threshold, i.e. for `0 ≤ c' < pq/2`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.matBox_corank_dominates_absZ_lt_top`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorankPure.lean` @ `4c439760`)
> - **Gloss.** `∫_{z∈Z} ∫_{Δ∈matBox p q T} ofReal((frobSq Δ + W z)^{−c'}) ∂vol ∂μ < ⊤`, given
>   `0 < p`, `0 < q`, `c' < (p*q : ℝ)/2`, `0 ≤ c'`, `0 < T`, `∀ z, 0 ≤ W z`, `μ Z < ⊤`. The corank
>   block `Δ` enters through its OWN squared Frobenius norm `frobSq Δ` (isotropic), on a non-negative
>   additive core `W z` that folds the deeper loss; the block peels at its Morse threshold `pq/2`.
> - **Proved.** The joint finiteness, unconditionally, at general opaque width `p × q` and over an
>   arbitrary measurable outer domain `(Ω, μ, Z)`. Axiom-clean `[propext, Classical.choice,
>   Quot.sound]` (**S2-free** — no `monomial_rlct`).
> - **Assumed.** None beyond the stated hypotheses. `W z ≥ 0` is the honest hypothesis (the deeper
>   loss is non-negative); `μ Z < ∞` (the outer box has finite volume, banked
>   `paramsBoxM_volume_lt_top`); `c' < pq/2` is the block-codim charge.
> - **Cited.** None (no external citation). Rides the banked flat corank-2 terminal
>   `radial_morse_dominates_absZ_lt_top` (`RouteMSchurDepth2`) and the banked `p × q → Fin (p·q)`
>   measure-preserving flatten (`eMatFlat`, `frobSq_eq_flatSum`, `matBox_eq_eMatFlat_preimage`,
>   `RouteMSJCorankResidual`) — all in-repo, S2-free.
> - **Deferred (NOT done here; named).**
>   (i) removing the **anisotropy** `Δ ↦ Δ · Q_b` (the Gram change of variables putting the true
>   `frobSq(C·Q̃_p + Γ·Q_b)` into isotropic `frobSq Δ + core` form) — the `(S,J)` change-of-variables
>   content;
>   (ii) accumulating the per-layer radial monomial `∏ uⱼ²` across layers (the recursion carrier
>   `SJState`, deferred to the mountain build);
>   (iii) `sjJointResolution` itself (needs the full recursion driving to this terminal). This brick is
>   the **reusable terminal** the recursion reaches, not the recursion.
> - **Structure & ideas observed.** The pointwise-in-`z` anisotropic bound is DEAD (documented finding
>   `genm-sjpeel-blow`, `RouteMSJCorankResidual` header): for rank-deficient `Q_b` the inner
>   `∫ frobSq(Δ·Q_b)^{−c'}` DIVERGES once `2c' ≥ M₀`, so the peel is NOT `lintegral_mono_ae` on a
>   pointwise estimate. This brick is the FINITE isotropic counterpart: once anisotropy is removed, the
>   block's own energy `frobSq Δ` on a non-negative core is joint-finite — the pure route keeps `Δ` a
>   chart coordinate and blows up its radial (charge `= pq`), NEVER integrating `Δ` out against `Q_b`
>   (which manufactures the divergent Gram det — the atom false wall). Confirms verdict-A at the
>   integral level for the isotropic terminal.
> - **Route.** matrix-flatten `eMatFlat` transports the inner block box integral to the flat Morse box
>   (helper `matBox_frobSq_add_lintegral_eq`, factored from `matBox_corank_residual_le`'s first calc
>   step); `lintegral_congr` over `z` then reduces the goal to the banked flat abstract-`Z` dominance
>   `radial_morse_dominates_absZ_lt_top` (the `z`-independent inner bound `Kbound (pq) c' T` pulled out
>   against `μ Z`). ~60 LoC, S2-free.
> - **Status.** sorry-free (pending reviewer fidelity check).

## Supporting lemma (same module)

> **`DLNFibre.DLN.RLCT.matBox_frobSq_add_lintegral_eq`** — `∫_{matBox p q T} (frobSq D + w)^{−c'} =
> ∫_{morseBox (p·q) T} (∑ᵢ xᵢ² + w)^{−c'}`, the `eMatFlat` transport of the block-box integrand to the
> flat Morse-box integrand (the shared first step of the banked `matBox_corank_residual_le`, factored
> for reuse). Axiom-clean `[propext, Classical.choice, Quot.sound]`.

## Build / hygiene

- `scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJCorankPure` — green (8285 jobs), zero errors, zero
  `sorry` in the module, zero long-line warnings.
- Forced `#print axioms` on both theorems: `[propext, Classical.choice, Quot.sound]` (clean-three;
  **S2-free**, `monomial_rlct` absent — the chart-geometry hygiene the guarded watch requires).
- Name-clash: `matBox_frobSq_add_lintegral_eq`, `matBox_corank_dominates_absZ_lt_top`,
  `RouteMSJCorankPure` all unique across `DLNFibre/` (`rg`, no clash). NOT wired into the single-writer
  `DLNFibre.lean` — **controller to wire** `import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankPure` after
  the `RouteMSJCorankPeel` import (before `AxCheck`).

## Guarded-watch verdict (the controller's key question)

The opaque-width `corankStep` (banked `RouteMSJCorankStep`, sorry-free, S2-free) DOES reach
`u²·(pivot energy + corank-decremented Schur residual)` at general `Fintype` widths — the (2,2,2)
`Case111`/`Case222` templates LIFT to opaque widths. **Verdict A holds at the chart-algebra level, in
Lean.** The isotropic terminal Morse peel is now banked at general `p × q` over an arbitrary outer
domain (this card). The guarded-watch risk locus (opaque-width `corankStep` cannot reach
`(monomial)²·unit` on a finite cover) is **NOT hit**: the pointwise algebra is done, and the isotropic
terminal is finite. The remaining gap is the **recursion carrier + anisotropy removal** (the `(S,J)`
double induction), NOT a chart-algebra wall — the atom false-wall route is avoided.
