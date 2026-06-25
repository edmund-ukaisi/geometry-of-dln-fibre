# Statement card — `(4,4,2,2)` hfin upper bound (S2-FREE), reshape sorry CLOSED

> **Claim.** For `c' < ½·minAdm M4422 = 2`, the flat-coordinate box integral of the threshold density
> `|routeMCore M4422|^{−c'}` over the open box `(−1,1)^28` is finite:
> `∫⁻_{routeMBaseNbhd M4422} |routeMCore M4422 x|^{−c'} < ⊤`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMCore_M4422_threshold_lt_top`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteM4422Hfin.lean` @ `<uncommitted — controller pins SHA>`;
>   base merge `66ae6588`).
> - **Gloss.** `routeMCore M4422` is the DLN square-Frobenius loss `frobSq (A0·A1·A2)` for the dimension
>   vector `M4422 = (4,4,2,2)` in flat coordinates (`A0 : 4×4`, `A1 : 4×2`, `A2 : 2×2`, 28 free entries).
>   For any `c'` strictly below the achiever threshold `½·minAdm M4422 = 2`, integrating `loss^{−c'}` over
>   the open coordinate box `(−1,1)^28` is finite. This is the `cover_le` (upper-bound, hfin) atom of
>   `routeMLayerCover_of_atoms` for `M = (4,4,2,2)`.
> - **Proved.** The full statement, unconditionally, sorry-free. Route: the open box is dominated by the
>   closed cube `[−1,1]^28` (monotone, integrand ≥ 0); transported through `paramsEquivFlat` (MP) to the
>   `Params M4422` box; split into the three per-layer matrix boxes via `eParams4422` (an MP
>   `piFinSuccAbove`/`piUnique` reshape, in `(A2,A1,A0)` order); Tonelli (`setLIntegral_prod`) to the
>   iterated integral; closed by the banked S2-free iterated-fibre core `triple_fibre_lt_top`
>   (`fibre_lintegral_mul_le` peels A0 then A1, terminating at the A2 4-dim radial Morse leaf). The `c'=0`
>   case is the trivial constant-1 integral over the finite-volume box.
> - **Assumed.** `c' < ½·minAdm M4422` (the achiever threshold; `minAdm M4422 = 4` computed by `decide`).
> - **Cited.** none. **S2-FREE**: `#print axioms = [propext, Classical.choice, Quot.sound]` — no
>   `monomial_rlct`, no `sorryAx`. (The fibre engine + radial Morse terminal `radial_ball_iff` are
>   Mathlib-only; no normal-crossing monomial RLCT citation.)
> - **Deferred.** none for `(4,4,2,2)`. (Note: this iterated-fibre route is **special-class** — it does
>   NOT generalize to corank-≥2 binding `M` per thread-27 `iterfibre-route-cert.md`; the general-M hfin
>   needs the rank-stratified `{V=0}` resolution, which remains the open long pole.)
> - **Status.** sorry-free, axiom-clean (S2-free). Awaiting reviewer fidelity confirmation.

## What this closes

The single open `sorry` in `RouteM4422Hfin.lean` (`routeMCore_M4422_threshold_lt_top`, the `Params`-reshape
identification) is now PROVED. The `(4,4,2,2)` hfin upper bound is the companion of the banked
box-divergence lower-bound atom `routeM4422_box_diverges` (`RouteM4422.lean`); together they are the two
analytic atoms of `routeMLayerCover_of_atoms` for `M = (4,4,2,2)`.

## New reusable API (in `RouteM4422Hfin.lean`)

- `paramsEquivFlat_decode` — the flat-decode `paramsEquivFlat H A (equivFin idx) = A idx.1.1 idx.1.2 idx.2`
  (re-derived locally to avoid the `Deepest*` import clash on `continuous_dlnLoss`).
- `eParams4422` / `measurePreserving_eParams4422` — the MP split `Params M4422 ≃ᵐ (A2 × (A1 × A0))` via
  `piFinSuccAbove` + `piUnique` (the function-space family, NOT the `Matrix` wrapper, which fails instance
  synthesis). Components `.1 = A 2`, `.2.1 = A 1`, `.2.2 = A 0` (definitional).
- `eParams4422_preimage_box` / `paramsEquivFlat_preimage_box4422` — the box-image lemmas.
- `frobSq_prod_eq_eParams4422` — the integrand identity via `prod_M4422_eq_rmatMul`.

The reshape pattern (open→closed box monotone; `paramsEquivFlat` MP to `Params` box; `piFinSuccAbove`/
`piUnique` layer split to per-layer matrix boxes in the fibre-peel order; Tonelli) is the template for any
future iterated-fibre hfin instance in the MATCH-class.
