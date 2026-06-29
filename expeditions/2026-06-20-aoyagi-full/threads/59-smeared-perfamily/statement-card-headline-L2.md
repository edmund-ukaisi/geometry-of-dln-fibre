# Statement card — the L=2 conditioned-box boundary-smeared box-divergence headline

The L=2 boundary-SMEARED achiever box-divergence (validate-small), as a per-family ASSEMBLY over a
CONDITIONED source box, with the worked `(2,3,1)` chart as the non-vacuity witness.

---

> **Claim (the assembly).** For `M : Fin (L+1) → ℕ` with `routeMAmbient M = n + 1`, the boundary-smeared
> achiever box integral `∫⁻_{cubeBox N ε} |routeMCore M x|^{−c'} = ⊤` follows from the per-family chart
> facts on a CONDITIONED source box `condBox p box δ` (pivot `p ∈ Ioo 0 δ`, every other coord `k` in a
> supplied interval `box k`): `ψ` measure-preserving + a measurable embedding; `R` a radial blow-up with
> fderiv `D`, injective on the box, `|det D u| = |u p|^h`; the containment `condBox ⊆ (ψ∘R)⁻¹(cubeBox ε)`
> (field A); the decode-derived peeled rate `routeMCore M (ψ(R(insertNth p z y))) = z²·Uy y` ON the
> conditioned box with `Uy` measurable and positive THERE and the conditioned rest box positive-measure;
> and `(h:ℝ) − 2c' ≤ −1`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMCore_box_diverges_smearedL2`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedHeadlineL2.lean` @ `012af98b`)
> - **Gloss.** Wraps the banked ∀M smeared contract (`routeMCore_box_diverges_smearedContract`) for the
>   L=2 conditioned box: the contract's weighted-divergence `hSdiv` is produced from the peeled quadratic
>   rate over the conditioned rest box by the conditioned axis-peel `condBox_weighted_diverges` /
>   `hSdiv_of_peeled_rate_onBox` (the generalization of genm-smeared2's full-box
>   `smearedSubBox_weighted_diverges` / `hSdiv_of_peeled_rate` to any positive-measure conditioned rest
>   box, via the same banked `axisPeel_diverges_of_quadratic_rate`). One `Fin (n+1)`↔`Fin N` dimension
>   cast isolated in the `subst`-clean `hSdiv_box_transport`.
> - **Proved.** The full reduction of the L=2 conditioned-box headline to the named per-family chart facts,
>   sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]` (forced recompile + `#print axioms`).
>   The conditioned axis-peel `condBox_weighted_diverges` and the conditioned `hSdiv_of_peeled_rate_onBox`
>   are proved in full (the M-agnostic `axisPeel` engine over an arbitrary positive-measure rest box).
> - **Assumed.** The per-family chart facts are carried as NAMED hypotheses: the MP/measurable-embedding
>   `ψ`, the radial `R`'s C¹/injOn/`|det|=|u p|^h`, field-A containment, the peeled rate + `U`-positivity
>   ON the conditioned box, the conditioned box's positive measure, and the exponent bound. These are the
>   opaque-width chart DECODE outputs + the analytic Λ₀-conditioning — supplied per family (the generic
>   constructions are independent follow-ups).
> - **Cited.** none new (measure theory; the cited `monomial_rlct` atom enters only the box-divergence's
>   1-D `rpow` atom inside the banked `axisPeel`, not this assembly).
> - **Deferred.** The generic opaque-width construction of `ψ`/`R`/the decode (the per-family peeled rate)
>   + the generic conditioned Λ₀-bound (field A). These are carried as hypotheses here; their from-scratch
>   opaque-width derivations are the separate follow-up (the `(2,3,1)`→opaque chart-map lift). The L≥3
>   front-prefix-product (`prodAux_front_peel`) is a separate sub-tide.
> - **Status.** sorry-free (awaiting reviewer fidelity check).

---

> **Claim (non-vacuity witness).** The conditioned-box assembly FIRES on the worked `(2,3,1)` chart:
> `∫⁻_{cubeBox 9 ε} |routeMCore M231 x|^{−c'} = ⊤` for `c' ≥ ½·minAdm M231 = 1`, every `ε > 0`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeM231sm_box_diverges_via_condBox`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedHeadlineL2Inst.lean` @ `012af98b`)
> - **Gloss.** Instantiates `routeMCore_box_diverges_smearedL2` with `M := M231`, `n := 8`, the banked
>   `(2,3,1)` chart maps (`psi231`/`R231`/`D231`), the conditioned `box231 δ` (coords 0,4 — the rank-block
>   diagonal — in `[δ/2,δ]`, the rest in `[−δ/8,δ/8]`), and the `subBox231`-conditioned facts. The peeled
>   rate / `U`-positivity ride on the banked `subBox231_det_ne` / `subBox231_U_pos` via the membership
>   bridge `insertNth ⟨6,_⟩ z y ∈ subBox231 δ` and the inclusion `condBox ⟨6,_⟩ (box231 δ) δ ⊆ subBox231 δ`.
> - **Proved.** The assembly's hypothesis bundle is jointly SATISFIABLE — ruling out the conceptual-slop
>   trap (a vacuous would-be-headline). Sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.
>   Reproduces `routeM231sm_box_diverges` (the banked `(2,3,1)` headline) through the conditioned interface.
> - **Assumed / Cited / Deferred.** none beyond the banked `(2,3,1)` chart's (all proved in
>   `RouteM231Smeared`).
> - **Status.** sorry-free (awaiting reviewer fidelity check).

---

## Soundness finding (why a CONDITIONED box, not the banked `smearedSubBox`)

The genm-smeared2 GENERIC interface (`smearedSubBox p δ` + `hSdiv_of_peeled_rate` +
`routeMCore_box_diverges_on_smearedSubBox`) is **too weak** to compose with the real rational-shear chart:
`smearedSubBox` pins the pivot in `Ioo 0 δ` but ALL other coords in the FULL `Icc −δ δ`, and
`axisPeel_diverges_of_quadratic_rate` requires `hUpos : 0 < Uy y` for ALL `y` in that full rest box. But
the unit `U = ‖P₁·H̄‖²` is `0` where the rank block `P₁ = 0` (the all-small corner of the full box), so
`hUpos` over the full box is UNSATISFIABLE and the off-pole rate degenerates (`det P₁ = 0`, the shear
cancellation breaks). An assembly built on it would be VACUOUS (green ≠ right). The `(2,3,1)`/`(1,3,2)`
precedents avoid this by feeding a CONDITIONED box (`subBox231`: the rank-block diagonal in `[δ/2,δ]`,
`det P₁ ≥ δ²/8 > 0`) — which `condBox` generalizes to opaque widths, keeping the assembly non-vacuous.

The fix did NOT touch the banked `smearedSubBox` (no collateral — it is used only by the re-routed
headline); it needs a conditioning predicate to be non-vacuous for the rational-shear branch, which the
conditioned `condBox` route supplies.
