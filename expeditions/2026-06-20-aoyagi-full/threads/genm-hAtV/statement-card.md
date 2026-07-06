# genm-hAtV — the corrected D1 ≥-leg route WIRED; LEAF-2 reduced to the explicit-core crux

Charged to build the EXPLICIT-CORE D1 ≥-leg producer `hAtV` (genm-d1l2close2 corrected roadmap): retire
the germ-discarding two-IFT-peel producer, route through the EXPLICIT homogeneous core `dlnLoss (H−r) 0`.

## Outcome

The **corrected architecture is WIRED, green, axiom-clean, and pushed** (`origin/genm-hAtV`). The whole
L=2 D1 ≥-leg is reduced to ONE precisely-stated, TRUTH-CONFIRMED crux `d1ge_L2_hAtV_explicit`. The
previously-BLOCKED `hCore` is now PROVEN clean (not via the germ-discarded residual, but via Aoyagi
Theorem 4 on the explicit core). The crux itself — the explicit Schur-complement chart transfer — is
isolated as the sole remaining `sorry`; it is a fresh multi-file sub-tide (the general-`v` analogue of
the deepest-point `DeepestGaugeChart` build), NOT a further gate on the abstract `Ψsymm` residual.

## Files

- **NEW** `lean/DLNFibre/DLN/RLCT/Validate/D1L2ExplicitCoreProducer.lean` (the producer module).
- **EDITED** `lean/DLNFibre/DLN/RLCT/Validate/HeadlineL2Assembly.lean` — `hD1ge_L2` bare `sorry`
  REMOVED, now wired to `d1ge_L2_deepestPoint_via_explicit_core_genL`; import added; docstring updated.
- Controller to wire `D1L2ExplicitCoreProducer` into the aggregator `DLNFibre.lean` (single-writer) +
  `AxCheck.lean`.

## Theorems delivered (all sorry-free unless noted)

- `dlnLoss_zero_smul` / `prod_smul_pow` / `prodAux_smul_pow` — full (all-layer) degree-`2L` homogeneity
  of the deepest core `dlnLoss M 0`. Clean-three.
- `flatNodeLoss_smul` + `measurable_flatNodeLoss` — the flat shadow feeding `deepest_le_of_homogeneous_core`.
- `rlctAtOn_dlnLoss_zero_flat` — `rlctAtOn (dlnLoss M 0) P = rlctAtOn (flatNodeLoss M) (paramsEquivFlat P)`
  (transport via `rlctAtOn_comp_homeomorph` + `paramsEquivFlatCLE`).
- **`core_zero_le_of_params`** — the Params-domain Aoyagi Theorem 4 (the previously-BLOCKED `hCore`):
  `rlctAtOn (dlnLoss M 0) 0 ≤ rlctAtOn (dlnLoss M 0) P` for ANY reduced-core `P`. Clean-three
  `[propext, Classical.choice, Quot.sound]`. Discharged by the homogeneity comparison, NOT a
  residual-value identity.
- **`d1ge_L2_hAtV_explicit`** — the SOLE `sorry` (the crux). Statement TRUTH-CONFIRMED (analytic Codex
  xhigh + sympy at (4,4,4)/r=1). `∃ P, nRegL2 H r / 2 + rlctAtOn (dlnLoss (H−r) 0) P ≤ rlctAt H (dlnLoss H B) v`.
- `d1ge_L2_deepestPoint_via_explicit_core` (`Fin 3`) + `_genL` (general-`L`, `hL2/hLlt`-pinned) — the
  `HeadlineL2Assembly.hD1ge_L2` drop-in, assembling the three pieces via banked
  `deepest_le_of_optimal_via_L2_ge`.

## Axiom footprint (forced `#print axioms`)

- `aoyagi_learning_coefficient_L2` : `[propext, sorryAx, Classical.choice, Quot.sound, monomial_rlct]`.
  `sorryAx` = the crux ONLY. **NO `hbox`** — L = 2 closes UNCONDITIONALLY (the deepest value uses the
  banked hbox-free `r1_resolution_interface_L2_generic`; the D1 leg dominates the core by Theorem 4,
  never computing an `M'`-degraded value). When the crux lands → clean-four
  `[propext, Classical.choice, Quot.sound, monomial_rlct]` (the mission target).
- `core_zero_le_of_params` : `[propext, Classical.choice, Quot.sound]`.

## The crux, precisely (the isolated remaining piece)

`d1ge_L2_hAtV_explicit`: at optimal `v`, produce `∃ P : Params (H−r)` with
`nRegL2 H r / 2 + rlctAtOn (dlnLoss (H−r) 0) P ≤ rlctAt H (dlnLoss H B) v`.

**Confirmed math (Codex xhigh + sympy):** pick a common invertible `r×r` minor of the layers at `v`
(exists — every partial product has `rank ≥ r`; front WLOG → top-left). Block `A0 = [[X,Y],[Z,W]]`,
`A1 = [[S,T],[U,V]]`; on `{det X ≠ 0, det M11 ≠ 0}` the regular coords `p = (M11−I, M12, M21)`
(dim `= nRegL2`) separate, and the slice residual at `p=0` is EXACTLY `‖A0red · A1red‖² =
dlnLoss (H−r) 0 (A0red, A1red)`, `A0red = W − Z X⁻¹ Y`, `A1red = V − U M11⁻¹ M12` (Schur complement
`M22 − M21 M11⁻¹ M12 = A0red A1red`; sympy `‖Δ‖ ≈ 1e-15`). Purely algebraic (polynomial + rational in
`det X, det M11`); NO existence-only `Ψsymm`. Dimension gap `flatDim − nReg − dimParams(H−r) =
r(2 H1 − r)` (= 7 at (4,4,4)/r=1) ⟹ the map is a SUBMERSION with FLAT directions.

**Reduction (all analytic bricks BANKED):** the crux reduces — via banked
`rlctAt_ge_nReg_add_slice_of_residual` — to the EXPLICIT Schur chart transfer
`hchart_explicit : rlctAt v = rlctAtOn (∑ p.1² + ∑ qₑ²) (0, t0)` (`qₑ` the `Ψsymm`-free Schur residual).
Given it, `rlctAtOn (∑ qₑ(0,·)²) t0 = rlctAtOn (dlnLoss (H−r) 0) P` by:
- `rlctAtOn_spectator_peel` (`S1Spectator`) — peels the FLAT directions. **This IS the "flat-direction
  Fubini" brick the coordinator/Codex flagged as load-bearing — it is ALREADY BANKED** (peels a product
  spectator factor, genuine Tonelli, `integrable_prod_iff_of_indep`).
- `rlctAtOn_comp_homeomorph` — the essential linear reindex.
- `rlctAtOn_unit_invariant_aux` — the bounded Gram/Jacobian unit (non-vanishing per modelidwit's
  Gram-sandwich verdict; carries none of hbox's order-4 pathology).
Then `core_zero_le_of_params` (Theorem 4, PROVEN) dominates `P`.

**THE WALL (isolated):** `hchart_explicit` — certifying the explicit rational corner-elimination map as
a LOCAL MEASURABLE CHART with the essential/flat split + bounded-unit Jacobian (Codex step 5). The
general-`v` analogue of the deepest-point `DeepestGaugeChart` multi-file build (which lands the same
chart at the ORIGIN, for rank-`r`-exact layers). A fresh ~600–1500-line sub-tide. Base case of the
∀-L `rlctAt_deepest_le_of_optimal` (Skeleton:1172, same recursion — the design lifts).

## Route-A vs the two-peel route (why this supersedes)

Route A (this tide): first peel only → `dlnLoss (H−r) 0` at a nonzero `P`, DOMINATED by Theorem 4.
Route B (retired two-peel): a SECOND peel of `P` to a degraded `dlnLoss M' 0`, needing the germ-value
identity `rlctAtOn(slice-of-q₂) = lambdaCore(M')` — which is BLOCKED (the `Ψsymm` germ discard,
genm-d1l2close2). Route A never computes an `M'` value: `core_zero_le_of_params` dominates ANY `P`, so
the whole degraded-core / R1@M' machinery is UNNEEDED. Strictly simpler (Codex-confirmed), and
unconditional at L=2.

## Consults / corroboration

- Codex xhigh (`codex/crux-prompt.md`, `codex/crux-answer.md`): Route A sound + strictly simpler; the
  explicit Schur decomposition; step-5 chart-certification is the wall; flat-Fubini is the single new
  analytic brick (found already banked as `rlctAtOn_spectator_peel`).
- modelidwit cert (`threads/genm-modelidwit/model-id-cert.md`): bounded non-vanishing Gram unit;
  submersion (not diffeo) shape; L=2 unconditional. Integrated into Route A (which needs only the
  Theorem-4 domination, a subset of modelidwit's stronger degraded-core identification).
- sympy: Schur reduction `‖Δ‖ ≈ 1e-15` at (4,4,4)/r=1 middle-stratum witness.
