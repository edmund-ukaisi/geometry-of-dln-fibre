# Statement card — STEP-1 terminal: `monomial × (unit ≥ 1)` lifts to general widths (option a)

Thread `genm-sjcarrier2` (tide, off `origin/genm-sjclose` @963a76de). Branch `genm-sjcarrier2`.
Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJTerminal.lean`. First sub-tide of the `SJState`
recursion carrier (the R1-UPPER final gate → `sjJointResolution`, `RouteMSJResolution.lean:803`).

> **Claim (STEP-1 verdict).** The `(2,2,2)` `monomial × (unit ≥ 1)` terminal
> (`Case222Resolution.blockForm_step3` + `step3_unit_ge_one` +
> `Case222Cover.integrableOn_monomial_mul_unit_iff`) — **option (a)** of the route-correction finding
> — **LIFTS to general (opaque `Fintype`) widths**. The three ingredients are general-width or
> `d`-generic; the only remaining work is the STEP-2 carrier that DRIVES the recursion to a terminal
> chart (not the terminal itself).
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
> - **Assumed.** none beyond the pin hypothesis (`c₀ ≤ |(M·Q) i j|`) and the standard unit bound
>   (`a ≤ |unit| ≤ b`, `0 < a`) the terminal statements carry. Those hypotheses are DISCHARGED, on a
>   terminal chart, by the STEP-2 carrier (which resolves rank-deficiencies until an entry is pinned).
> - **Cited.** none new. Rides the banked `frobSq_smul_mul`/`corankStep_prefactor`
>   (`RouteMSJCorankStep`), `integrableOn_monomial_mul_unit_iff`/`monomialIntegrand_integrable_of_lt`
>   (`Case222Cover`) — all in-repo, clean-three.
> - **Deferred.** The `SJState` recursion carrier (STEP 2) — driving `corankStep` + STEP-3's
>   block-elimination down the layers (accumulating `∏ uⱼ²`), resolving the rank-deficient-`Q_b`
>   charts (the standing `L ≥ 3` recursion), to REACH a terminal chart with a pinned entry — and
>   `sjJointResolution` (`RouteMSJResolution.lean:803`) itself, UNTOUCHED. This is the multi-week
>   mountain; this module supplies only the terminal it lands on and the terminal's finiteness.
> - **Status.** sorry-free (awaiting fidelity review).

## STEP-1 verdict — option (a) LIFTS

The route-correction finding left the controller to re-decide between (a) the `monomial × unit`
terminal and (b) the pure isotropic peel for a post-identity-channel free-matrix layer. This tide
verifies **(a) lifts**. Evidence, ingredient by ingredient:

1. **Monomial factoring — banked, ALREADY general widths.** `frobSq ((u • M) · Q) = u² · frobSq (M · Q)`
   is `RouteMSJCorankStep.frobSq_smul_mul` (opaque `Fintype`); the accumulated `∏ bᵢ²` prefactor rides
   through by `corankStep_prefactor` (sequential-independence). Nothing width-specific.
2. **Unit lower bound — generalises cleanly.** The `(2,2,2)` `step3_unit_ge_one`'s `unit ≥ 1` came from
   ONE entry pinned to `1` in the dehomogenised blow-up chart. At general widths this is
   `frobSq X ≥ (X i j)²` (`frobSq_ge_sq_entry`), so a pinned entry `|·| ≥ c₀ > 0` gives `frobSq ≥ c₀²`.
   No width dependence.
3. **Terminal finiteness — `d`-generic.** `integrableOn_monomial_mul_unit_iff` (unit-factor
   threshold-invariance) and `monomialIntegrand_integrable_of_lt` (below-threshold monomial
   finiteness) are both stated for arbitrary `d`; `terminal_monomial_mul_unit_integrable` composes
   them. The exceptional-divisor exponents summing to `≥ minAdm` is the banked charge-budget
   (`minAdmRec_eq_minAdm`, piece 6, sorry-free), so `c' < ½·minAdm ⟹ c' < monomialThreshold` on the
   terminal chart.

**No option-b fallback needed.** The `(2,2,2)` mechanism is the isotropic-blind terminal that survives
at general widths; the pure isotropic peel (`RouteMSJCorankPure`) is retained only for the
identity-channel / full-rank sub-charts (per the route-correction), not the general degenerate strata.

## What STEP-1 does NOT do (the STEP-2 carrier — the mountain)

The terminal statements carry a **pin hypothesis** (`c₀ ≤ |(M·Q) i j|`) and the **bounded-unit
hypothesis**. On the general degenerate strata these are NOT free: when the non-pivot rows `Q_b` of the
downstream product are rank-deficient (the standing `L ≥ 3` wall, 750/5440 charts per the
`sjJointResolution` docstring), the residual entry can vanish and the pin is lost — those charts
recurse to a deeper `corankStep`. The STEP-2 carrier is exactly the machinery that drives the recursion
(accumulating `∏ uⱼ²` via `corankStep_prefactor`, block-eliminating via STEP-3) down the layers until a
terminal chart with a pinned entry is reached, on which this module's terminal + finiteness fire. That
carrier is the multi-week mountain; it is UNTOUCHED here (this is the first sub-tide).
