# Statement card — `genm-sjbuild` (R1-UPPER decorated recursion, predicate layer)

**Status:** sorry-free (pieces 1, 3, 4 + shape + API pins). **Module:**
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDecoratedRec.lean` (204 lines, NOT yet wired into the aggregator).
**Build:** green in the worktree (`scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRec`, forced
recompile 7.5s). **Axioms (forced `#print axioms`):** `carrierThreshold_shift`, `binding_334`,
`binding_2222`, `carrierThreshold_334` — all `[propext, Classical.choice, Quot.sound]` (clean three; NO
`sorryAx`, NO `monomial_rlct`, NO `cited_aoyagi_dln`). **Pinned SHA:** built on `origin/genm-sjbuild`
@ `ff61adb6` (over `expedition/aoyagi-full` @ `d9b8a7ea`).

## STEP-0 gate (prerequisite, banked separately)

`step0-terminal-bridge.md` — GATE PASS (decorrelated-Codex-confirmed). The terminal count↔monomial bridge
`½·minAdm(remChain) ≤ monomialThreshold d (sharedDivisorExp) jac` is UNIFORM over all route terminals; on
the three named anchors it holds VACUOUSLY (they are regime-A/B + free-matrix clean, the monomial terminal
is never reached). No re-scope.

## Delivered results (this module)

| Lean name | statement (gloss) | status |
|---|---|---|
| `carrierThreshold N` | `½·minAdm N` — the count-level RLCT budget of the remaining chain | def |
| `carrierThreshold_nonneg` | `0 ≤ carrierThreshold N` | proved |
| `carrierThreshold_shift` | `carrierThreshold M − ½·peelCharge M u ≤ carrierThreshold (redChain u M)` (piece 4, the peel-charge soundness cast; = banked `half_minAdm_sub_half_peelCharge_le`) | proved |
| `binding_334` | `(3,3,4)` cut `t=1`: `peelCharge + minAdm(redChain) = 4+4 = 8 = minAdm` — soundness-gate TIGHTNESS (NOT predicate inhabitation) | proved (`decide`) |
| `binding_2222` | `(2,2,2,2)` cut `t=1`: `1 + 2 = 3 = minAdm` — soundness-gate tightness | proved (`decide`) |
| `binding_3334` | `(3,3,3,4)` cut `t=1`: `4 + 3 = 7 = minAdm` — soundness-gate tightness (STEP-0 deeper-product anchor) | proved (`decide`) |
| `carrierThreshold_334` / `_2222` | the anchor budgets `= 4` / `= 3/2` | proved |
| `SJDecoration N` | the decoration: banked `SJLinGenState` carrier (shared-divisor support + linear residual) + Jacobian exponents `jac` + chart domain (pieces 2) | structure (shape pinned) |
| `DecoratedBoxThresholdFinite N D` | the decorated finiteness predicate `∀ c' < carrierThreshold N, ∫_dom ∫_{unitBox d} (∏u^{jac})·(carrier.loss)^{−c'} < ⊤` (piece 3, the load-bearing inductive object; GENERATOR-CARRIER loss, NOT a separable Gram weight) | def (shape pinned) |
| `APIPins` (5 `example`s) | durable contracts confirming the banked bricks the mountain consumes exist with expected types: the soundness gate `minAdm_le_peelCharge_add_redChain`, regime A `matBox_corank_residual_absZ_le`, regime B `matBox_corank_dominates_absZ_lt_top`, the monomial terminal `sjLoss_terminal_lintegral_lt_top`, the base connection `loss_ofMatrix_product` | proved (type-pinned) |

## Fidelity notes (for the reviewer)

- **`carrierThreshold` is indexed by the CURRENT chain `N`, not a `PartialProfile`.** The outer spine
  `routeMBoxThresholdFinite_of_step` already does arity strong-induction on `N`, so `N = remChain π` and the
  Σ-typed profile is redundant. The cert's "content is the load-bearing part; names to finalise" latitude.
- **`SJDecoration.ν` is the active-variable INDEX (Fintype); `x : ν → ℝ` are its coordinates.** The active
  block integrates over `ν → ℝ` (not `ν`); the spectator `ζ` is a value type with a `MeasureSpace`. `dom :
  Set (ζ × (ν → ℝ))`. (First build surfaced the `loss`-arity mismatch; corrected.)
- **The predicate's loss IS `SJLinGenState.loss`** (the r1predicate HEADLINE, decorrelated-confirmed) —
  generator-by-generator monomial-prefix × linear-residual — NOT the separable
  `Wπ(u)·frobSq(prod(remChain))^{−c'}` (the divergent pointwise route on the rank-deficient-`Q_b` locus).
- **`SJDecoration` omits the cert's `meas`/`domFin` fields.** `dom` carries no measurability/finiteness
  constraint yet; those enter as hypotheses in the unbuilt proofs (pieces 5–7). Acceptable for a shape pin;
  flagged by the fidelity review.

## Fidelity review (`d5030719`, reviewer + decorrelated Codex): SURVIVED, one CONCERN, no defect

- **Predicate + axioms + naming: SOUND / CLEAN.** Loss is the generator-carrier (headline honored); `dom :
  Set (ζ × (ν→ℝ))` is a fidelity fix over the cert's `Set (ζ × ν)`; forced `#print axioms` clean-three on all
  results; `sjJointResolution` untouched.
- **CONCERN (accepted, artifacts corrected):** the STEP-0 "uniform over ALL terminals" headline overclaimed.
  Corrected to: the NARROW threshold-definition decision (`carrierThreshold = ½·minAdm`, decoration-free) is
  sound; on load-bearing charts the bridge is an INEQUALITY `½·minAdm ≤ threshold` with no counterexample
  (23358 charts, `step0_ineq.py`), NOT a tight equality (`(4,4,2)`: 8 > 7), and NOT yet a banked Lean theorem
  for the actual multi-divisor terminal — `routeLayerAtlas_value` is the idealized single-divisor model, and
  the actual-terminal bridge is the UNPROVEN piece-6 obligation. The `binding_*` docstrings were narrowed to
  the arithmetic they prove (soundness-gate tightness, not route content / inhabitation).

## NOT delivered (the mountain — reported, not laundered)

The genuinely-new CoV plumbing (~65–75% new): **piece 5** `decorated_peel_step` (anisotropy removal at
opaque widths, clear-first ordering, the `c'=pq/2` boundary ε-argument), **piece 6** `decorated_base`
(terminal + the count↔monomial bridge), **piece 7** `routeMBoxThresholdFinite_of_decorated` (the `π=∅`
consumer discharging `sjJointResolution`). `sjJointResolution` (`RouteMSJResolution.lean:797`) remains the
single named sorry, UNTOUCHED. The banked bricks these consume are type-pinned in `APIPins`.
