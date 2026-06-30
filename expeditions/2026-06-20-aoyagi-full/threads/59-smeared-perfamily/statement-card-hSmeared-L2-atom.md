# Statement card — the spine's `hSmeared` slot at L=2, as a NAMED atom

The R1-LOWER ∀M achiever box-divergence SPINE
(`RouteMAchieverDispatch.routeMCore_box_diverges_achiever_spine`) discharges its BOUNDARY-SMEARED
branch through a hypothesis slot of shape
`hSmeared : ∀ _ : 2 ≤ L, BoundarySmeared M → BoxDiverges M c' ε`. This card records the named atom that
fills that slot at `L = 2`, for the sibling assembly tide (`genm-r1lower`) to plug into the spine.

The heavy content — the fully-unconditional square box-divergence brick layer — is documented in the
companion card [`statement-card-square-L2.md`](statement-card-square-L2.md)
(`routeMCore_smearedL2_square_uncond`, the Varah / Levy–Desplanques diagonal-dominance machinery). This
card is one rung above: the spine-slot WIRING + the square-stratum reduction that makes the wiring total.

---

## The named atom (the spine's `hSmeared` slot at L=2)

> **Claim.** For any `M : Fin 3 → ℕ` with `1 ≤ minAdm M`, any `c' ≥ ½·minAdm M`, `ε > 0`, the
> BOUNDARY-SMEARED branch's achiever box-divergence holds in exactly the curried shape the dispatch
> spine consumes:
> `(2 ≤ 2) → BoundarySmeared M → ∫⁻_{cubeBox (routeMAmbient M) ε} |routeMCore M x|^{−c'} = ⊤`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.hSmeared_L2`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedHSmearedL2.lean`)
>   + the applied convenience form `hSmeared_L2_apply` (the `2 ≤ 2` gate pre-discharged, takes
>   `hsm : BoundarySmeared M` directly).
> - **Signature.**
>   ```
>   theorem hSmeared_L2 (M : Fin 3 → ℕ) (hpos : 1 ≤ minAdm M) (c' : NNReal)
>       (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
>       (2 ≤ 2) → BoundarySmeared M →
>         ∫⁻ x in cubeBox (routeMAmbient M) ε,
>           ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤
>   ```
> - **Gloss.** `hSmeared_of_smearedChart` (the spine wiring from a chart-BUILDER) instantiated at
>   `L = 2` with the total square-stratum chart-builder `smearedChart_of_square`
>   (`fun hsm => smearedChart_of_square M hpos hsm`). The RHS is definitionally the spine's
>   `BoxDiverges M c' ε`.
> - **Proved.** sorry-free; forced `#print axioms` (scratch, olean force-elaborated) =
>   `[propext, Classical.choice, Quot.sound]` on BOTH `hSmeared_L2` and `hSmeared_L2_apply`. S2-FREE
>   (no `monomial_rlct`), no `sorryAx`, no new axiom.
> - **Assumed.** the spine's own branch conditions — `1 ≤ minAdm M` (the dispatch regime, top-level
>   spine hyp), `c' ≥ ½·minAdm M`, `ε > 0`. No analytic per-family hypothesis (those are discharged
>   inside the banked `routeMCore_smearedL2_square_uncond`).
> - **Cited / Deferred.** none.
> - **Status.** sorry-free; pending reviewer fidelity check + controller AxCheck/aggregator wiring.

## Why the wiring is TOTAL on the smeared-L=2 class (the square reduction — STEP-0 gate)

> **Claim.** At `L = 2`, in the spine's regime, EVERY `BoundarySmeared M` is the square-`P₁` stratum
> (`deepRank M = M 0`). So `smearedChart_of_square : BoundarySmeared M → SmearedAchieverChart M` is a
> TOTAL chart-builder on the class — no residual smeared-L=2 case escapes it.
>
> - **Lean chain (all banked, `RouteMSmearedSquareReduce.lean`).**
>   - `BoundarySmeared M = ¬InteriorDrop M ∧ deepRank M < deepRows M`, `deepRows M = M 1` (L=2).
>   - `widths_pos_of_minAdm` : `1 ≤ minAdm M ⟹ 0 < M 0, M 1, M 2`.
>   - `interiorDrop_L2_iff` : `InteriorDrop M ⟺ 0 < M 2 ∧ deepRank M < M 0 ∧ deepRank M < M 1`.
>   - `deepRank_le_M0` : `deepRank M ≤ M 0` (always, L=2).
>   - `smeared_deepRank_eq_M0` : `1 ≤ minAdm M ∧ BoundarySmeared M ⟹ deepRank M = M 0 ∧ 0 < deepRank M
>     ∧ 0 < M 2`. (`¬InteriorDrop` + `deepRank < M 1` + `M 2 > 0` ⟹ `¬(deepRank < M 0)` ⟹
>     `deepRank ≥ M 0`; with `deepRank ≤ M 0`, equality.)
> - **Verdict (STEP-0).** square-stratum coverage COMPLETE at L=2 — no gap, no fake-close. The light
>   wiring path the brief anticipated is the realised path; the fallback (`SmearedAchieverChart M`
>   builder ∀smeared-M-L2) is exactly `smearedChart_of_square`, already banked.
> - **Honest scope.** This is the L=2 smeared branch ONLY. `L ≥ 3` is out of scope (the spine's
>   `2 ≤ L` smeared branch at higher depth is a separate construction, not claimed here).

---

## Provenance / boundary

- Module owned by the `genm-r1smeared` tide: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedHSmearedL2.lean`
  (new; imports only `RouteMSmearedSquareReduce`). The assembly that plugs this into the spine
  (`RouteMLayerCoverGE` / `RouteMLayerCoverGEL2` / interior-chart files) is the `genm-r1lower` tide's
  domain — NOT touched here.
- Controller to wire: add the module import to the aggregator `DLNFibre.lean` and pin
  `#print axioms hSmeared_L2` (+ `hSmeared_L2_apply`) in `AxCheck.lean` (currently neither
  `smearedChart_of_square` nor the closer `hSmeared_squareSmeared_L2` is axiom-pinned in AxCheck).
