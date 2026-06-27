# Statement card — WALL 2: the BOUNDARY-CLEAN achiever chart discharges the box-divergence atom

> **Claim.** For a clean-boundary `M` — `NoInteriorBothDrop M` (no interior chain boundary drops both
> row and column rank), the clean equality `deepRank M = deepRows M`, `1 ≤ minAdm M`, all widths positive
> (`∀ s, 0 < M s`), and a nonempty deepest block `(deepestCoords M hL).Nonempty` — the achiever box
> integral diverges at and above the achiever threshold: for `c'` with `½·minAdm M ≤ c'` and every
> `ε > 0`, `∫⁻_{cubeBox N ε} |routeMCore M x|^{−c'} dx = ⊤`. The chart is the single radial blow-up
> `phi := pivotBlowupOn (deepestCoords M) (deepestPivot M)` of the deepest factor (the POLYNOMIAL-radial
> branch — no Schur shear, no rational pole).
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMCore_box_diverges_clean`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryCleanChartFull.lean` @ `c2e2f38e`)
>   - the assembled bundle `DLNFibre.DLN.RLCT.cleanNodeChart : NodeAchieverChart M`
>   - rate: `DLNFibre.DLN.RLCT.routeMCore_cleanPhi` (`RouteMBoundaryCleanRate.lean`)
>   - unit `U ≢ 0` a.e.: `DLNFibre.DLN.RLCT.cleanUbound` / `UPolyClean_ne_zero` (`RouteMBoundaryCleanU.lean`)
>   - cov / det: `DLNFibre.DLN.RLCT.cleanPhi_cov` / `cleanPhi_abs_det` (`RouteMBoundaryCleanChartFull.lean`)
>
> - **Gloss.** `routeMCore M = dlnLoss M 0 ∘ (paramsEquivFlat M).symm` is the square-Frobenius loss of the
>   layer product in flat coordinates. `cleanPhi` blows up the deepest-layer flat coords radially by one
>   pivot `u_p`. The chart factors the loss as `routeMCore (cleanPhi u) = (u_p)²·U(u)` with `U =
>   dlnLoss M 0 (unblownParams u)` (the `u_p`-stripped tuple) the `u_p`-free unit; the Jacobian is
>   `|det Dφ| = |u_p|^{minAdm−1}` (radial-coord exponent `= codim − 1 = minAdm − 1`, since
>   `(deepestCoords M).card = minAdm M`). Feeding the bundle to the M-agnostic divergence assembly
>   `routeMCore_box_diverges_of_nodeChart` gives the box divergence at threshold `½·minAdm M`.
>
> - **Proved.** All chart fields, sorry-free, for ∀M in the clean class (the listed hypotheses):
>   - RATE `routeMCore (cleanPhi u) = (u_p)²·U` — via the per-coordinate flattening decode
>     `paramsEquivFlat_symm_decode` (`= rfl` through `flatEquivOf_symm_coord`) + membership-only reasoning
>     (`flatCoordOf_mem_deepestCoords_iff`) ⟹ `cleanParams = scaleLayer u_p (deepLayer) (unblownParams)`
>     ⟹ banked `prod_scaleLayer` / `dlnLoss_homogeneous_layer` (`LossHomogeneity`).
>   - `U ≢ 0` a.e. — `U = eval u UPolyClean` (a coefficient-polymorphic chain product `cprod` + its ring-hom
>     `Matrix.map` naturality `cprod_map`), `UPolyClean ≠ 0` by the all-ones witness `u₁ ≡ 1` (every entry of
>     `unblownParams u₁` is `1`; the all-ones product has positive `(0,0)` entry), then
>     `MvPolynomial.ae_eval_ne_zero` (zero set Lebesgue-null) + `U ≥ 0`.
>   - det `|u_p|^{minAdm−1}` + cov — DIRECTLY the GENERIC `pivotBlowupOn` lemmas (`pivotBlowupOn_abs_det` at
>     `active.card = minAdm` via `deepestCoords_card_eq_minAdm`, `pivotBlowupOn_injOn`,
>     `lintegral_image_eq_lintegral_abs_det_fderiv_mul`). No null-slice split (the clean branch is the easy
>     polynomial cov — no rational pole).
>   - leaf-integrand, image containment, measurability, box-bound.
>
> - **Assumed (hypotheses the statement carries).** `NoInteriorBothDrop M`; `deepRank M = deepRows M`
>   (clean); `1 ≤ minAdm M`; `∀ s, 0 < M s` (all widths positive — needed for the all-ones witness `U > 0`
>   and for the non-vacuity of the loss); `(deepestCoords M hL).Nonempty` (the deepest block is nonempty,
>   so a pivot exists). NB `NoInteriorBothDrop M` is the CHAIN-NATIVE hypothesis the banked bricks use; the
>   `BoundaryClean ⟹ NoInteriorBothDrop` bridge (WALL 1) is OUT OF SCOPE / deferred to the assembly tide.
>
> - **Cited.** `monomial_rlct` (the S2 single-axis monomial divergence leaf), reached via the M-agnostic
>   assembly exactly as the `(4,4,2,2)` / `(3,3,4)` sibling instances. The chart pieces themselves are
>   S2-free (`[propext, Classical.choice, Quot.sound]`); only the atom headline carries `monomial_rlct`.
>
> - **Deferred.** The 3-way+L1 `nodeChartGeneral` assembly (CLEAN ∪ SMEARED ∪ INTERIOR ∪ L=1) that
>   discharges `routeMCore_box_diverges_achiever` for ALL `M` — this card delivers the CLEAN branch only.
>   The `BoundaryClean ⟹ NoInteriorBothDrop` chain-native bridge (WALL 1). The SMEARED branch (the
>   rational-pole cov). These are the assembly tide's, not WALL 2's. A concrete-`M` `example` instantiating
>   the WHOLE clean class in-module (`NoInteriorBothDrop` + clean + nonempty deepest block for a fixed `M`,
>   e.g. `(4,4,2,2)`) — natural in the assembly tide once WALL 1 is built, since `deepRank`/`deepestCoords`
>   are noncomputable and the clean-class predicates are most cheaply discharged via `BoundaryClean`. The
>   `(4,4,2,2)` end-to-end shape is already validated by `routeM4422_box_diverges` (sibling).
>
> - **Route (formaliser).** Option A (Codex-corroborated, `codex/architecture-answer.md`): keep `phi` as
>   the GENERIC flat→flat `pivotBlowupOn` (no outer reshape Q ⟹ det/cov are the generic lemmas directly);
>   pay the cost on the RATE, decoded ONCE via `paramsEquivFlat_symm_decode` then reasoned via membership.
>   The `U`-positivity uses the all-ones witness (`codex/upositivity-answer.md` Q3), reducing nonvanishing
>   to the all-ones-product positivity rather than re-deriving the product through the opaque decode.
>
> - **Status.** sorry-free + reviewed (fidelity PASS, independent reviewer + decorrelated Codex on the
>   five fidelity risks: rate-is-genuine-loss, genuine radial det/cov, honest all-ones witness, load-bearing
>   hypotheses, honest P/A/C/D split). Axiom-checked (force-elaborated `#print axioms`): chart pieces
>   `[propext, Classical.choice, Quot.sound]`, atom carries `monomial_rlct`. Validated on the `(4,4,2,2)`
>   banked anchor (the clean atom-discharge instantiates to the `routeM4422_box_diverges` shape).
>   Reviewer notes (report-only, non-blocking): (1) the three modules are NOT yet in the single-writer
>   aggregator `DLNFibre.lean` / `AxCheck.lean` — the controller wires them (manual clash-scan + a co-import
>   of the full `DLNFibre` with the three modules found no clash); (2) the `(4,4,2,2)` validation lives in
>   the sibling `RouteM4422`, not in-module — a one-line concrete-`M` `example` would harden non-vacuity.
