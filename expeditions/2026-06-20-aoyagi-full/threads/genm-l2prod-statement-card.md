# Statement card — `genm-l2prod` (L2 CoV-production): the good-chart endpoint + §8-positivity bricks

Thread `genm-l2prod`. Branch `genm-l2prod` @ `fe1d979f`. Files:
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCornerGate.lean`,
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJGoodLoss.lean`.

These are the LANDING (corner endpoint) + the §8-positivity CORE of the pinned good-chart route
(jbassembly cert). They do NOT close `sjJointResolution` — the change-of-variables / resolution map
connecting `gammaPeelIntegral` to the endpoint remains the mountain (see "Deferred").

---

> **Brick 1 — the §8 compactness gate.** A continuous `g : (Fin n → ℝ) → ℝ` strictly positive at
> every unit-sphere direction `ofLp ω` has a uniform positive lower bound `a > 0` with
> `a ≤ g (ofLp ω)` for all `ω`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.exists_pos_lower_bound_on_sphere`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCornerGate.lean` @ `fe1d979f`)
> - **Gloss.** Extreme value theorem on the compact unit sphere of `EuclideanSpace ℝ (Fin n)`: a
>   continuous function positive there attains a positive minimum (`IsCompact.exists_forall_le'`,
>   `isCompact_sphere`). Handles `n = 0` (empty sphere) uniformly.
> - **Proved.** Fully unconditional (given continuity + sphere-positivity).
> - **Assumed.** `Continuous g`; `0 < g (ofLp ω)` for all sphere directions.
> - **Cited.** none. **Deferred.** none.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

> **Brick 2 — corner endpoint with the §8 gate discharged by positivity+continuity.** For a
> continuous degree-2-homogeneous `g` positive on the unit sphere and `c' < n/2`, the cube-box
> integral `∫_{[-1,1]ⁿ} (g z)^{-c'} < ⊤`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.corner_block_cube_lintegral_lt_top_of_pos`
>   (`RouteMSJCornerGate.lean` @ `fe1d979f`)
> - **Gloss.** The banked `corner_block_cube_lintegral_lt_top` with its pre-extracted lower-bound
>   triple `(a, ha, hlb)` replaced by the natural hypothesis `0 < g (ofLp ω)` on the sphere; the
>   uniform bound is supplied internally by Brick 1.
> - **Proved.** Finiteness of the cube-box integral below `c' < n/2`.
> - **Assumed.** `g` continuous, degree-2-homogeneous, `> 0` on the sphere; `0 ≤ c' < n/2`; `NeZero n`.
> - **Cited.** none. **Deferred.** none.
> - **Status.** sorry-free, axiom clean-three.

> **Brick 3 — endpoint-admissibility of a squared-injective-linear loss.** For an INJECTIVE linear
> `L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)` and `c' < n/2`, `∫_{[-1,1]ⁿ} (∑ⱼ (L z)ⱼ²)^{-c'} < ⊤`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.corner_block_cube_lintegral_lt_top_of_injective`
>   (`RouteMSJCornerGate.lean` @ `fe1d979f`)
> - **Gloss.** The loss `‖L z‖²` of an injective linear map is a positive-definite quadratic form:
>   degree-2-homogeneous (L linear), continuous (finite-dim), and `> 0` off the origin (injectivity),
>   so Brick 2 applies. Collapses the good-chart endpoint's §8 + homogeneity + measurability
>   obligations to a single "L injective" hypothesis — the abstract shape `g_cc`/`g_T` reduce to.
> - **Proved.** Finiteness of the cube-box integral of the PD-quadratic-form loss below `c' < n/2`.
> - **Assumed.** `L` injective; `0 ≤ c' < n/2`; `NeZero n`.
> - **Cited.** none. **Deferred.** none.
> - **Status.** sorry-free, axiom clean-three.

> **Brick 4 — the good-chart cross-coupled map is injective.** The map
> `sjGoodMap (Γ, v) = (P·v·A₂, (C·v + Γ·W)·A₂)` underlying the resolved loss
> `g_cc(Γ, v) = frobSq (P·v·A₂) + frobSq ((C·v + Γ·W)·A₂)` (vslice cert §4a) is injective given the
> pivot `P` has a left inverse and `W, A₂` have right inverses.
>
> - **Lean:** `DLNFibre.DLN.RLCT.sjGoodMap_injective`, and the §8 payoff
>   `DLNFibre.DLN.RLCT.sjGoodMap_loss_pos` (`g_cc(Γ,v) > 0` for `(Γ,v) ≠ 0`); helper
>   `frobSq_pos_of_ne_zero` (`M ≠ 0 → 0 < frobSq M`)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJGoodLoss.lean` @ `fe1d979f`)
> - **Gloss.** Sequential kernel argument: first block + `P, A₂` invertible force `v = 0`; second
>   block with `v = 0` + `W, A₂` invertible force `Γ = 0`. Hence the cross-coupled Schur loss is a
>   positive-definite quadratic form on the good chart (pivot bounded below, deep factor generic),
>   which is the §8 positivity the endpoint needs.
> - **Proved.** Injectivity of `sjGoodMap`; strict positivity of `g_cc` off the origin. Pure matrix
>   algebra (`Matrix.mul_assoc`, left/right inverse cancellation, `frobSq_nonneg`).
> - **Assumed.** `LP·P = 1`, `W·RW = 1`, `A₂·RA = 1` — i.e. pivot left-invertible, `W` and `A₂`
>   full row rank (the good-chart hypotheses).
> - **Cited.** none.
> - **Deferred.** That the good chart (pivot bounded below via a refined `{|det pivot| ≥ δ·scale}`
>   cover, deep factor generic) actually SUPPLIES these inverses is the refined-cover construction,
>   NOT proved here.
> - **Status.** sorry-free, axiom clean-three.

---

## Not closed (the remaining mountain, named)

`sjJointResolution` (`RouteMSJResolution.lean:803`, `gammaPeelIntegral M t ρ κ c' < ⊤`) is UNCHANGED
(still the pre-existing sorry). The bricks above are the endpoint + §8-positivity core of the pinned
route; the connecting tissue is genuinely-new content (recon-map / Codex estimate ~65–75% new, a
multi-tide mountain), namely:

1. **The CoV / resolution map** — transporting the matrix double-integral
   `∫_{A'∈tailBox} ∫_{A₀∈matBox∩pivotChart} frobSq(A₀·Q)^{-c'}` to the flat corner-block integral
   `∫_{[-1,1]^{Mval}} (g_cc E_T)^{-c'}` (block-reindex + Schur split + shear D↦Γ + depth reduction +
   flatten of the joint block `E_T`). Banked pieces: `frobSq_schur_block_split`,
   `measurePreserving_shearSub`, `matReindexEquiv`, `eMatFlat`.
2. **The refined cover** `{|det pivot| ≥ δ·scale}` (good) ∪ deeper (small-pivot + `A_{L-1}`-rank-drop),
   which SUPPLIES Brick 4's inverse hypotheses on the good chart.
3. **The L-recursion over the rank flag** + **deeper-branch non-binding** (banked `sjChargeBudget_le`,
   `sjSubordination`; finite-flag termination).

Codex (decorrelated, xhigh, `threads/genm-l2prod/codex/`) confirmed: bank endpoint-admissibility +
the injective good-loss brick, then report the CoV as the mountain — the right leaf-executor move;
and flagged the good-chart reduction (candidate C3) as "the whole CoV in disguise", not tide-sized.

## Fidelity note

The bricks are named for exactly what they prove (endpoint finiteness / injectivity / positivity),
not for `sjJointResolution`. The identity `g_cc = frobSq(P·v·A₂) + frobSq((C·v+Γ·W)·A₂)` is the
vslice §4a / jbassembly §1b resolved cross-coupled form; that this equals `frobSq(A₀·Q)` on the good
chart (after the CoV) is DEFERRED, not asserted here.
