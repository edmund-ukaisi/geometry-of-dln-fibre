# Statement card — STEP-1 terminal: `monomial × (unit ≥ 1)` ENDPOINT lifts to general widths

Thread `genm-sjcarrier2` (tide, off `origin/genm-sjclose` @963a76de). Branch `genm-sjcarrier2`.
Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJTerminal.lean`. First sub-tide of the `SJState`
recursion carrier (the R1-UPPER final gate → `sjJointResolution`, `RouteMSJResolution.lean:803`).

> **Claim (STEP-1).** The **terminal ENDPOINT + its finiteness** of the `(2,2,2)`
> `monomial × (unit ≥ 1)` mechanism (`Case222Resolution.blockForm_step3` + `step3_unit_ge_one` +
> `Case222Cover.integrableOn_monomial_mul_unit_iff`) **LIFTS to general (opaque `Fintype`) widths** as
> **conditional bricks** (carrying a pinned-entry + bounded-unit hypothesis). The three ingredients are
> general-width or `d`-generic. The `(2,2,2)` case they subsume binds at **corank 1**.
>
> **Scope (NOT claimed; escalated).** These bricks do NOT establish that the general degenerate strata
> (corank ≥ 2 / `L ≥ 3`) reduce to this endpoint. The repo's certificates
> (`verify-r1-shortcut.md`: one-blow-up ⟹ `u²·unit` false for `L ≥ 3`; `verify-r1-diagb-334.md`:
> `(3,3,4)` corank-2 undercount at a binding stratum) show that needs Aoyagi's coupled `diag(b)`
> resolution with shared exceptional variables — genuinely-new (`outer-construction-cert.md` "THE WALL"),
> deferred. This endpoint is what that resolution's normal-crossing OUTPUT lands on.
>
> - **Lean:** `DLNFibre.DLN.RLCT.frobSq_ge_sq_entry`, `frobSq_ge_of_entry`,
>   `frobSq_ge_one_of_entry_eq_one`, `frobSq_terminal_radial`, `frobSq_terminal_radial_prefactor`,
>   `terminal_monomial_mul_unit_integrable`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJTerminal.lean`).
> - **Gloss.**
>   - `frobSq_ge_sq_entry` : `(M i j)² ≤ frobSq M` — the unit lower bound, ANY entry, general widths
>     (`frobSq = ∑ᵢⱼ Mᵢⱼ²` is a sum of nonneg squares). The general-width mechanism behind the
>     `(2,2,2)` `step3_unit_ge_one`'s `+ 1`.
>   - `frobSq_ge_of_entry` : `c₀ ≤ |M i j| → 0 ≤ c₀ → c₀² ≤ frobSq M` (pinned coordinate `⟹` unit `> 0`).
>   - `frobSq_ge_one_of_entry_eq_one` : `M i j = 1 → 1 ≤ frobSq M` (the pinned dehomogenised
>     leading/pivot coordinate).
>   - `frobSq_terminal_radial` : `frobSq ((u • M) · Q) = u² · frobSq (M · Q) ∧ c₀² ≤ frobSq (M · Q)`
>     given `c₀ ≤ |(M · Q) i j|`, `0 ≤ c₀` — the general-width `blockForm_step3` + `step3_unit_ge_one`
>     lift (monomial factoring + unit bound). Prefactor form `frobSq_terminal_radial_prefactor`
>     carries the accumulated `∏ bᵢ²` through.
>   - `terminal_monomial_mul_unit_integrable` : `monomialIntegrand d k h c' · |unit|^{−c'}` is
>     `IntegrableOn (unitBox d)` for `c' < monomialThreshold d k h` (`0 < c'`, `unit` bounded in
>     `[a,b]`, `0 < a`) — the `d`-generic finiteness endpoint, composing the banked
>     `integrableOn_monomial_mul_unit_iff` + `monomialIntegrand_integrable_of_lt`.
>   - `terminal_monomial_mul_unit_lintegral_lt_top` : the `∫⁻ … ENNReal.ofReal (monomialIntegrand · |unit|^{−c'}) < ⊤`
>     form of the above (via `lintegral_ofReal_ne_top_iff_integrable`) — the `∫⁻`-shape the recursion's
>     inner integral actually lands on. `monomialIntegrand_nonneg` supports it.
> - **Proved.** All eight, sorry-free. Non-vacuity in-file: the packaged `frobSq_terminal_radial` at
>   `Fin 2` (`M̂ = [[1,a1],[a2,a3]]`, `Q = [[1,0],[0,1]]`, pinned `(0,0)` entry `= 1`); the `(2,2,2)`
>   `step3_unit_ge_one` residual `= frobSq [[1,a1],[q+a2,q·a1+a3]]` with `(0,0) = 1`, so
>   `frobSq_ge_one_of_entry_eq_one` recovers its `≥ 1`. `#print axioms` = `[propext, Classical.choice,
>   Quot.sound]` (clean-three) for all eight; S2-free; **no `monomial_rlct`** (forced `#print axioms`
>   confirms no S2 axiom entered).
> - **Assumed.** the pin hypothesis (`c₀ ≤ |(M·Q) i j|`) and the standard unit bound
>   (`a ≤ |unit| ≤ b`, `0 < a`) the terminal statements carry. These are DISCHARGED (on the
>   normal-crossing output chart) by the deferred coupled `diag(b)` resolution — NOT by a naive
>   per-layer descent (see SCOPE below); for corank ≥ 2 the naive descent fails.
> - **Cited.** none new. Rides the banked `frobSq_smul_mul`/`corankStep_prefactor`
>   (`RouteMSJCorankStep`), `integrableOn_monomial_mul_unit_iff`/`monomialIntegrand_integrable_of_lt`
>   (`Case222Cover`) — all in-repo, clean-three.
> - **Deferred.** The `SJState` recursion carrier (STEP 2) — Aoyagi's coupled `diag(b)` resolution with
>   shared exceptional variables (`outer-construction-cert.md` "THE WALL"; genuinely-new for corank ≥ 2,
>   NOT a naive per-layer `corankStep` descent) — and `sjJointResolution` (`RouteMSJResolution.lean:803`)
>   itself, UNTOUCHED. This module supplies only the normal-crossing terminal that resolution's output
>   lands on, and the terminal's finiteness.
> - **Status.** sorry-free; Lean reviewed SURVIVED; verdict prose re-scoped after the fidelity finding.

## What STEP-1 establishes (the terminal ENDPOINT, general widths)

The three ingredients of the `monomial × (unit ≥ 1)` endpoint, and why each lifts:

1. **Monomial factoring — banked, ALREADY general widths.** `frobSq ((u • M) · Q) = u² · frobSq (M · Q)`
   is `RouteMSJCorankStep.frobSq_smul_mul` (opaque `Fintype`); the accumulated `∏ bᵢ²` prefactor rides
   through by `corankStep_prefactor` (sequential-independence). Nothing width-specific.
2. **Unit lower bound — generalises cleanly.** The `(2,2,2)` `step3_unit_ge_one`'s `unit ≥ 1` came from
   ONE entry pinned to `1` in the dehomogenised blow-up chart. At general widths this is
   `frobSq X ≥ (X i j)²` (`frobSq_ge_sq_entry`), so a pinned entry `|·| ≥ c₀ > 0` gives `frobSq ≥ c₀²`.
   No width dependence.
3. **Terminal finiteness — `d`-generic.** `integrableOn_monomial_mul_unit_iff` (unit-factor
   threshold-invariance) and `monomialIntegrand_integrable_of_lt` (below-threshold monomial
   finiteness) are both stated for arbitrary `d`; `terminal_monomial_mul_unit_integrable` (+ its
   lintegral form) composes them. Given the exceptional-divisor exponents sum to `≥ minAdm` (the banked
   charge-budget `minAdmRec_eq_minAdm`, piece 6, sorry-free), `c' < ½·minAdm ⟹ c' < monomialThreshold`.

## SCOPE — what STEP-1 does NOT establish (fidelity finding, escalated to the controller)

The reviewer (SURVIVED on the Lean; clean-three, `sjJointResolution` untouched) flagged that the
earlier verdict prose ("option (a) lifts for the general degenerate strata; no option-b needed")
OVERCLAIMED. Corrected:

- The terminal bricks are **conditional** — they carry the pin hypothesis (`c₀ ≤ |(M·Q) i j|`) and the
  bounded-unit hypothesis. The `(2,2,2)` case they subsume binds at **corank 1** (residual `Δ` a scalar).
- For the **general degenerate strata (corank ≥ 2 / `L ≥ 3`)**, discharging those hypotheses is NOT a
  naive per-layer descent. The repo's own pen-and-paper certificates refute the naive reduction:
  `theory/aoyagi-2023-reproduction/verify-r1-shortcut.md` (one-blow-up ⟹ `u²·unit` FALSE for `L ≥ 3`;
  `(2,2,2,2)` `t=(1,0,0)` leaves a fresh lower-depth non-unit core), `verify-r1-diagb-334.md`
  (`(3,3,4)` binding corank-2: true `rlct = 4` but a threshold-only / per-row model undercounts to `3`,
  at a stratum that SETS the RLCT), `verify-r1-light-recursion.md` (per-row model holds only corank ≤ 1).
- The correct general-width target is Aoyagi's **coupled `diag(b)` resolution with shared exceptional
  variables** (`outer-construction-cert.md` "THE WALL" — genuinely-new resolution-of-singularities
  content, NOT measure-plumbing labor). Its normal-crossing OUTPUT (`∑ bᵢ²` on a chart where one `b_i`
  divides the rest) IS a monomial × (unit ≥ 1) — the endpoint this module supplies. So the endpoint is
  route-agnostic and correct; REACHING it is the deferred coupled resolution.
- **CONTROLLER RE-DECIDE.** The mission premised STEP-2 on "drive `corankStep` down the layers, apply the
  terminal at the bottom" (a per-layer descent). The certificates say corank ≥ 2 needs the coupled
  `diag(b)` (shared support), which is genuinely-new. STEP-2 should be scoped to that coupled resolution,
  not a naive descent. `sjJointResolution` (`RouteMSJResolution.lean:803`) is UNTOUCHED (this is the
  first sub-tide); the carrier is the multi-week mountain, and its corank-≥2 core is a genuine wall, not
  labor. Codex (decorrelated) concurred with this re-scope.
