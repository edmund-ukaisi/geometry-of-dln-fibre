# Statement card — `genm-sjcarrier` (R1-UPPER final gate: anisotropy + recursion carrier → `sjJointResolution`)

Tide: `genm-sjcarrier` (branch `genm-sjcarrier`, off `origin/genm-rblowuppure` @`12fc0a76`). Target: the
last peel sorry `sjJointResolution` (`RouteMSJResolution.lean:803`), via piece 1 (anisotropy removal /
"joint Gram c.o.v.") then piece 2 (the `SJState`/`sjRunMin` recursion carrier).

**Outcome: INFRA banked; a decisive, triply-decorrelated ROUTE finding that re-aligns the mission onto
verdict A. `sjJointResolution` left UNTOUCHED (honest sorry, not laundered).** No Lean discharge this
tide — building the mission's literal piece-1 route would have banked the DEAD/walled route.

---

## INFRA (done)

- Wired `import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankPure` into the worktree's `DLNFibre.lean` (after
  `RouteMSJCorankPeel`, before `AxCheck`). `+2` lines.
- `scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJCorankPure` — green (8285 jobs, 0 errors, 0 sorries in
  module).
- Name-clash gate (mission-sanctioned: isolated green + `rg` under `hstep2chain` contention): `rg` over
  `DLNFibre/` confirms the 3 top-level names (`matBox_frobSq_add_lintegral_eq`,
  `matBox_corank_dominates_absZ_lt_top`, `matBox_corank_residual_absZ_le`) are unique. The import is a
  LEAF add (nothing imports it), so it cannot break downstream. Full heavy `scripts/lb DLNFibre` NOT
  fired (respecting the ≤2-heavy-builds cap with `hstep2chain` live); rg + leaf-isolation suffice.
- `scripts/sorries`: `RouteMSJResolution.lean` shows its single bare `sorry` at line 803
  (`sjJointResolution`) — UNTOUCHED. `RouteMSJCorankPure.lean` shows 0.
- Branch pushed: `git push origin HEAD:genm-sjcarrier` (fresh branch).

## THE FINDING — the mission's piece 1 ("joint Gram c.o.v. `Γ↦Γ·Q_b`") is the WRONG route

**Claim (triply-decorrelated).** The Gram change of variables `Γ ↦ Γ·Q_b` CANNOT land the bottom-block
residual `frobSq(C·Q̃_p + Γ·Q_b)` in the weight-free isotropic `frobSq Δ + W z` form that the pure peels
(`matBox_corank_dominates_absZ_lt_top` / `matBox_corank_residual_absZ_le`) consume. It inevitably produces
the `det(Q_b Q_bᵀ)^{−p/2}` Gram-Jacobian (ATOM) form (`gammaAtom_aniso_shifted_eq`) — the route
`pure-vs-atom-adj.md` (verdict A) and `outer-construction-cert.md` adjudicate as DEAD / walled on the
degenerate strata. Doing the c.o.v. "jointly over `(A₀,A')`" does NOT rescue it: on the positive-measure
rank-deficient-`Q_b` locus (`L ≥ 3`) the full-rank Gram formula does not apply, and integrating its
`det^{−p/2}` weight over `A'` is finite ONLY via a genuinely-new joint principalisation of
`det(Q_bQ_bᵀ)=‖∧^q Q_b‖²` for a matrix PRODUCT `Q_b` — the "resolution-of-singularities, NOT
measure-theoretic plumbing" wall named in `outer-construction-cert.md`.

**Three independent confirmations.**
1. **Rigorous algebra.** `Γ↦Γ·Q_b` gives an isotropic image quadratic ONLY when `Q_b` is square-invertible,
   and THEN with Jacobian `|det Q_b|^{−p} = det(Q_bQ_bᵀ)^{−p/2}` — the Gram weight is unavoidable. A
   weight-free `frobSq Δ + W` requires NOT mapping `Γ` through `Q_b` (keep `Γ`=`Δ` isotropic). So piece 1
   as stated ("Gram c.o.v. → isotropic weight-free form") is internally contradictory.
2. **Design certs (banked, decorrelated p&p + Codex).** `pure-vs-atom-adj.md` VERDICT A: "DO NOT discharge
   the general-`L` outer integral via the atom (`gammaAtom_aniso_shifted_eq`) followed by an outer
   `A'`-integral of the Gram-det — that route hits the full-space over-count wall on the degenerate
   strata. DO use the PURE radial `(S,J)` recursion" (Γ a chart coordinate, NO Gram-det ever forms).
3. **Fresh decorrelated Codex xhigh** (`codex/route-{prompt,answer}.md`, leaning withheld): "using Gram
   c.o.v. to obtain `frobSq Δ + W` with plain Lebesgue `dΔ dA'` is a category error, except in the trivial
   orthonormal-row case … `Γ↦Γ·Q_b` is the wrong first step. It moves the proof into the Gram-Jacobian
   world, where degeneracy of `Q_b` is a real obstruction requiring extra resolution data. Route P (pure
   radial) is the route aligned with that isotropic endpoint."

## THE REFRAME (actionable) — how the anisotropy is REALLY removed (pure route, verdict A)

The mission's INTENT (remove anisotropy so the isotropic pure peels apply) is right; the MECHANISM is the
pure route's per-step reduction (`chart-lemma-probe.md`, the green-lit general-`L` spec), NOT the Gram
c.o.v.:

- **Step 2 (banked): the single radial factor.** `corankStep` (`RouteMSJCorankStep`):
  `frobSq((u•fromBlocks A B C D)·Q) = u²·(frobSq(A·Q̃_p) + frobSq(C·Q̃_p + Γ·Q_b))`. `u` factors cleanly;
  charge = block codim (`radial_morse_residual_power_le`).
- **Step 3 (THE remaining hardest brick): the `Z`-independent unit block-elimination.** Reduce the
  normalised block `D_J' → [[1,O],[O,D_{J+1}]]` by det-1 row/col transforms that depend ONLY on the block
  (not on the downstream `Z`), absorbed into the ADJACENT factor `C^{(S+1)}` (deeper factors untouched, by
  product associativity). The loss becomes `‖pivot rows‖² (Morse — THIS is the isotropic `frobSq Δ`) +
  ‖D_{J+1}·(reduced downstream)‖² (folds into the deeper core `W`)`. The `(2,2,2)` instance is banked
  (`Case111`/`Case222`); lifting to opaque widths is the brick. `chart-lemma-probe.md` + decorrelated
  Codex: "large chart algebra, NOT resolution-of-singularities" (bounded; verdict A does not flip).
- **Terminal / intermediate shapes (banked, wired this tide): the pure peels.**
  `matBox_corank_dominates_absZ_lt_top` (`c' < pq/2`, `W ≥ 0`, terminal) and
  `matBox_corank_residual_absZ_le` (`c' > pq/2`, `W > 0`, exponent shift `c'↦c'−pq/2`) — the isotropic
  JOINT per-step shapes `∫_{z∈Z}∫_{Δ∈matBox}(frobSq Δ + W z)^{−c'}` the recursion consumes. `Δ` enters via
  its OWN Frobenius norm (weight-free) — reachable ONLY by step 3, never by the Gram c.o.v.
- **Base / endpoint (banked):** `sjBase1_freeMatrix`, `monomialIntegrand_integrable_of_lt`, charge
  bookkeeping (`minAdmRec_eq_minAdm`, `sjChargeUpdate_accum`, `sjSubordination`, threshold monotonicity).

## THE CONTROLLER QUESTION (blocks piece 2 — the recursion carrier)

`outer-construction-cert.md`: the PLAIN `sjJointResolution` IH (`hIH : ∀ M', RouteMBoxThresholdFinite M'`)
"cannot be the recursion vehicle" for the ATOM route — that route needs a DECORATED `I_π(s)` object
carrying the Gram-weight + a divisor-support table (a contract re-scope the cert assigns to the
CONTROLLER). BUT that analysis is for the ATOM route (which carries the Gram-weight). The PURE route
(verdict A, `chart-lemma-probe`) reaches a monomial `(∏ b_i²)·(unit)` with NO surviving Gram determinant
— so the decoration may be UNNECESSARY, and the carrier may be definable against the current plain
`sjJointResolution` contract via the `SJState`/`sjRunMin` running-min invariant already stubbed.

**Decision the controller must make before piece 2 (the `SJState` carrier) can be built:**
pure route (no Gram-weight decoration; the carrier is `diag(b)·[E_J|D_J]·∏_{s>S}C` driving `corankStep`
down the layers via step-3 block-elimination) vs the decorated `I_π(s)` re-scope. The pure route is
verdict A's recommendation and keeps `sjJointResolution`'s plain contract; it is gated on the step-3
brick (general-width `Z`-independent unit block-elimination), which is genuinely-new large chart algebra
(bounded per verdict A), NOT a Gram c.o.v.

## Why nothing was banked into the peel this tide (honest-partial)

- Building the mission's literal piece 1 (Gram c.o.v.) would bank the DEAD/walled atom route — anti-bedrock.
- The correct next step (step-3 relative corank-step invariant at general widths) is genuinely-new large
  chart algebra AND is gated on the controller's plain-vs-decorated contract decision (defining a new
  decorated contract is the controller's re-scope call, not a leaf executor's).
- The banked machinery already covers the per-step ALGEBRA (`corankStep`) and the terminal SHAPES (pure
  peels, just wired); what is missing is exactly the recursion carrier tying them together — the
  genuinely-new work gated on the decision above.
- `sjJointResolution` left UNTOUCHED (single honest sorry at `RouteMSJResolution.lean:803`); NOT laundered.

## Files

- `lean/DLNFibre.lean` (+2: wired `RouteMSJCorankPure` import). Green in isolation; leaf add.
- `expeditions/aoyagi-full/threads/genm-sjcarrier/codex/route-{prompt,answer}.md` (decorrelated Codex xhigh
  route check).
- `expeditions/aoyagi-full/threads/genm-sjcarrier/statement-card.md` (this card).

## Build / hygiene

- `scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJCorankPure`: green (8285 jobs).
- `scripts/sorries`: `sjJointResolution` (RouteMSJResolution:803) is the sole bare sorry in that module,
  untouched; `RouteMSJCorankPure` 0 sorries. `RouteMSJCorankPure` is S2-free (banked, forced `#print
  axioms` clean-three per `genm-rblowuppure` card).
- No name clashes (`rg`). Full `scripts/lb DLNFibre` deferred (heavy-build cap; leaf-import + rg suffice).
