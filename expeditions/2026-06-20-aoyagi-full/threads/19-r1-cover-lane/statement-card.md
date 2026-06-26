# Thread 19 — R1.6 cover lane (general-M `IsRouteMCover`, the LOWER bound)

The R1 gate (`resolution_charts`) was reduced by the prior tide to EXACTLY one residual: a general-M
`IsRouteMCover (routeMCore M) (routeMBaseNbhd M) (routeLayerAtlas M).ι (layerD M) (layerK M) (layerH M)`
(`resolution_charts_of_layerCover`). This thread targeted that cover.

## Outcome: PARTIAL — the cover WALLS on two analytic atoms; the generalizable parts are banked

The (2,2,2) hand-built cover atoms do NOT generalize directly. Assessment + decorrelated Codex
(gpt-5-codex, high, 2026-06-24) agree the residual is the genuine R1.6 resolution geometry. Banked: the
three structural `IsRouteMCover` fields for general M, the general per-leaf interior positivity, the
`cover_le` RHS-positivity, and a sorry-free ASSEMBLY reducing the full cover to the two residual atoms.

---

> **Claim.** For general layer-width `M : Fin (L+1) → ℕ`, the three structural fields of `IsRouteMCover`
> over `routeMCore M` / `routeMBaseNbhd M` hold; the `cover_le` RHS-sum over the layer family is `≠ 0`;
> and GIVEN the two analytic atoms (below-threshold finiteness `hfin` + ε-uniform box divergence `hdiv`),
> the full `IsRouteMCover` over the layer family `(routeLayerAtlas M).ι, layerD M, layerK M, layerH M` holds.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMLayerCover_of_atoms` (+ `layerCover_Fmeas`, `layerCover_Uopen`,
>   `layerCover_Umem`, `monomialIntegrand_pos_on_interior`, `layerCover_rhs_ne_zero`)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCover.lean` @ `f50d7ef9`)
> - **Gloss.** `routeMLayerCover_of_atoms M hfin hdiv : IsRouteMCover (routeMCore M) (routeMBaseNbhd M)
>   (routeLayerAtlas M).ι (layerD M) (layerK M) (layerH M)` — the exact family
>   `resolution_charts_of_layerCover` consumes. `hfin`: whenever the layer leaf-sum
>   `∑ᵢ ∫_{[0,1]^{dᵢ}} ofReal(monomialIntegrand)` is finite, `∫_{(−1,1)^N} ofReal(|routeMCore|^{−c'}) < ⊤`.
>   `hdiv`: when `c'` is at-or-above some leaf threshold, `∫_{[−ε,ε]^N} ofReal(|routeMCore|^{−c'}) = ⊤`
>   for every `ε>0`.
> - **Proved (unconditional).** The three structural fields (`Fmeas`/`Uopen`/`Umem`) for any M; the leaf
>   integrand is `>0` wherever no coordinate vanishes (`monomialIntegrand_pos_on_interior`); the leaf-sum
>   RHS `≠ 0` for the layer family, any M (`layerCover_rhs_ne_zero`). All axiom-clean
>   (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`).
> - **Assumed (the assembly's hypotheses).** `hfin` (below-threshold finiteness of the loss integral over
>   the box) and `hdiv` (ε-uniform box divergence). These are HONEST hypotheses, not discharged — pinned to
>   the exact `routeMCore M` / layer-family `(d,k,h)`. Reviewer (2026-06-24) confirmed both are non-vacuous
>   and cannot be trivially/​vacuously satisfied (no trap-iii smuggle).
> - **Cited.** none here. (The `rlct = ½·codim` reading downstream rides the cited Aoyagi/Watanabe bound,
>   unchanged.)
> - **Deferred (the genuine R1.6 mountain).** The two atoms `hfin`/`hdiv`. The (2,2,2) template does not
>   generalize: (`hdiv`) the single-explicit-chart `monomial·unit` factorization is a depth-2 miracle (the
>   Jacobian tower is non-triangular for `L>1`); the PROVEN squeeze `rlctAtOn = nReg/2 + rlctAtOn(reduced)`
>   computes `rlctAtOn` additively — the WRONG shape for the box-integral `=⊤` field, and a single-path
>   squeeze does not give the MIN-over-branches lower bound. (`hfin`) the obstruction is COMPLETENESS —
>   the pivot charts must COVER the box `(−1,1)^N` up to a null set; iterating `recStep` does not package it.
> - **Status.** sorry-free + reviewed (fidelity, 2026-06-24: FAITHFUL, no drift/smuggle/overclaim).

## R1 gate state

`resolution_charts` (`Skeleton.lean`) still carries `sorryAx` — the gate is NOT closed (the two atoms
remain open). `resolution_charts_of_layerCover ∘ routeMLayerCover_of_atoms` is the proven path from the
two atoms to the gate; discharging the atoms is the remaining work.

## Where the next lane should aim

- **Lower bound (`hdiv`):** build the `rlctAtOn`→box-integral-divergence bridge so the PROVEN squeeze
  descent (`schur_recursion_step_squeeze` + `rlctAtOn_layerReduced_transport`) can supply `hdiv` along the
  achiever path — plus the MIN-over-branches argument (no branch undershoots). This is the certified route;
  building explicit Jacobian towers for general depth is the dead end.
- **Upper bound (`hfin`):** an inductive measurable-cover / partition statement for the recursively
  generated pivot charts over the box (the "no missing strata" completeness), then reuse the per-leaf
  finiteness machinery branch-wise.
- A clean NON-VACUITY witness within reach: the `L=1` / two-width case (`M : Fin 2`), where
  `routeMCore = ∑ xᵢ²` (sum of squares, no blow-up) — would fire the assembly on an infinite family and
  reproduce `minAdm/2`. Not built here (separate sub-build; does not change the wall).
