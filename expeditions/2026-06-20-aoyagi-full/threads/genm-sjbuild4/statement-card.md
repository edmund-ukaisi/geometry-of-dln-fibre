# Statement card — R1-UPPER `genm-sjbuild4`: the S2-free monomial-threshold lower bound + monument scope verdict

Thread `genm-sjbuild4` (formaliser). Branch `genm-sjbuild4` (pushed to `origin`, commit `c975639f`).
Base `expedition/aoyagi-full @0144680e`. One new module, isolated force-recompiled green
(`scripts/lb`), NOT wired into the `DLNFibre.lean` aggregator (controller wires). Forced
`#print axioms` = clean-three `[propext, Classical.choice, Quot.sound]`; S2-FREE (no `monomial_rlct`,
no `cited_aoyagi_dln`). `scripts/sorries` = 0 in the module; no name clashes with siblings.

## What LANDED — `RouteMSJMonomialLower.lean` (the constructive S2-free RLCT lower bound)

> **Claim.** The weighted-monomial RLCT threshold is bounded below by the per-axis minimum,
> **without** the S2 citation `monomial_rlct` — the finiteness direction of S2, proved directly from
> Mathlib for general `d` and arbitrary `(k, h)`.
>
> - **Lean headline.**
>   `iInf_axisRatio_le_monomialThreshold (d : ℕ) (k h : Fin d → ℕ) :`
>   `  (⨅ j, axisRatio (h j) (k j)) ≤ monomialThreshold d k h`.
> - **Gloss.** `monomialThreshold d k h = sSup {c | ∃ c' : NNReal, c = c' ∧ IntegrableOn (monomialIntegrand
>   d k h c') (unitBox d)}`. For every `c' : NNReal` strictly below the per-axis minimum
>   `⨅_j (h_j+1)/(2 k_j)`, the integrand `(∏_j |u_j|^{h_j})(∏_j |u_j|^{2 k_j})^{−c'}` is integrable on
>   `[0,1]^d`; hence `c'` lies in the `sSup` set, so `⨅ axisRatio ≤ sSup = monomialThreshold`
>   (`ENNReal.le_of_forall_nnreal_lt` + `le_sSup`).
> - **Proof spine (all sorry-free, clean-three):**
>   - `abs_rpow_lintegral_Ioo_lt_top` — single-axis convergence `∫⁻_{(0,ε)} |x|^s < ∞` for `−1 < s`
>     (finite companion of the banked `abs_rpow_lintegral_Ioo_eq_top`; Mathlib
>     `intervalIntegral.integrableOn_Ioo_rpow_iff`).
>   - `prod_rpow_lintegral_Ioo_box_lt_top` — the `Fin d` product convergence over the open box
>     `(0,ε)^d`, all axis-exponents `> −1` (the `piFinSuccAbove` induction + `setLIntegral_prod` +
>     `ENNReal.mul_lt_top`; the convergent mirror of the banked divergent
>     `prod_rpow_lintegral_Ioo_box_eq_top`).
>   - `restrict_unitBox_eq_open` — boundary-null bridge: the closed and open unit boxes have equal
>     volume `1`, so their restricted measures agree.
>   - `monomialIntegrand_lintegral_unitBox_lt_top` — closed-box `∫⁻` finite below the per-axis minimum.
>   - `axisRatio_lt_exp` — per-axis: `(c' : ℝ≥0∞) < axisRatio h k ⟹ −1 < (h:ℝ) − 2 k c'`.
>   - `monomialIntegrand_integrableOn_of_lt_axisRatio` — the `IntegrableOn` element of the `sSup` set.
> - **Proved.** All, sorry-free; forced `#print axioms` clean-three on the headline and on
>   `monomialIntegrand_integrableOn_of_lt_axisRatio`.
> - **Fidelity / precision.** Name = content: this is a LOWER bound on `monomialThreshold`, the
>   finiteness (integrability) half of S2. It does NOT prove the S2 *value equality*
>   `monomialThreshold = ⨅ axisRatio` (that needs the meromorphic-continuation / pole-order content
>   Lean lacks — the `monomial_rlct` axiom, and the banked `monomialThreshold_ge_of_mult` which routes
>   through it). It generalises the `(1,1,1)`-only `Case111Bridge.prodBox_rpow_integrableOn_iff`, whose
>   header explicitly flagged the general shape as "Lean labour, not mathematics."
> - **Why it is a terminal prerequisite.** The decorated recursion's terminal fires
>   `RouteMSJLedger.sjLoss_terminal_lintegral_lt_top`, whose hypothesis is
>   `c' < monomialThreshold d (sharedDivisorExp e) h`. Discharging that S2-free from the carrier
>   threshold `c' < ½·minAdm(remChain)` needs (i) `½·minAdm(remChain) ≤ ⨅ axisRatio` (a combinatorial
>   fact the recursion supplies, tying `sharedDivisorExp`/`h` to `remChain` — recursion-coupled, NOT
>   landed here) and (ii) `⨅ axisRatio ≤ monomialThreshold` — THIS module (decoupled from the recursion).

## What did NOT land — THE MONUMENT (`decorated_peel_step` → base → recursion) is ARCHITECTURALLY BLOCKED

The pinned `decorated_peel_step` / `decorated_base` / well-founded recursion → `RouteMBoxThresholdFinite M`
is **not buildable from the banked inventory**. `RouteMBoxThresholdFinite M` is NOT closed;
`sjJointResolution` (`RouteMSJResolution.lean:803`) is UNTOUCHED. The obstruction, verified concretely
against the banked structures:

1. **The banked decoration carrier cannot express the peel step.** `SJDecoration M` and its ONLY two
   operations — `radialAttach` (`RouteMSJDecorated`) and `rowMix` (`RouteMSJDecoratedRowMix`) — keep the
   deeper space `(Z, mZ, ctx, dom)` **fixed** and are **pointwise-loss** identities. There is NO banked
   operation that (a) maps a `z`-block of `Z` into fresh `u`-coordinates (the actual blow-up change of
   variables that consumes `Z` toward the monomial terminal), (b) integrates out a freed corank block via
   the regime atoms, or (c) descends the base chain / threshold. Concretely: after ANY sequence of
   `radialAttach`/`rowMix`, `decLoss u z` still depends on the full `z ∈ Z`, so it never reaches the
   `z`-independent monomial terminal `sjLoss e u`. Building the missing Z-block-peel / chain-descent
   carrier operation (with its measure change of variables) IS the monument — not a banked composition.

2. **Regime A needs a strict positive core.** `matBox_corank_residual_absZ_le` (regime A, `c' > pq/2`)
   requires the deeper core `W z > 0` STRICTLY. On the vanishing / rank-deficient locus `W = 0` it fails,
   forcing the recursive `W > 0` chart-tree stratification (further blow-up) — the shared-`Z` coupling the
   design cert (`genm-sjjoint-design/cert.md`) identifies as the unbuilt `(S,J)` integral-level content —
   which the banked structures do not support.

3. **The terminal-bridge inequality (piece 6) is recursion-coupled.**
   `½·minAdm(remChain) ≤ monomialThreshold d (sharedDivisorExp) jac` is NOT a standalone fact: `jac` and
   `sharedDivisorExp` must be TIED to `remChain` by the recursion's construction (for arbitrary `jac`/
   `sharedDivisorExp` the inequality is false). Its S2-free direction additionally needs the constructive
   lower bound landed above; the remaining `½·minAdm(remChain) ≤ ⨅ axisRatio` part depends on the
   recursion's terminal data.

This matches **three prior decorrelated verdicts** — the pen-and-paper design cert (`genm-sjjoint-design`,
exact `0/4000` binding-cut saturation data + Hölder-infeasibility), decorrelated Codex xhigh
(`genm-sjbuild3/codex/scope-answer.md`), and the `genm-sjbuild2/3` scope conclusions — all: the honest
close is the **unbuilt `(S,J)` integral-level double induction**, a multi-module resolution-of-singularities
construction that first requires a NEW chain-descending decoration carrier + a `remChain`-parameterised
predicate. Attempting a green `decorated_peel_step` from the current inventory would either build that
missing machinery (the mountain) or launder the gap via a black-box IH the design cert proved insufficient.
Per the mission stop-condition, STOPPED on the peel step and banked the one honest, reachable, decoupled
prerequisite instead.

## Re-scoping options for the controller (registered as direction, not prescription)

- Build the **new carrier**: a chain-descending decoration (a `remChain` field + a Z-block-peel operation
  performing the regime-A/B measure change of variables) and a `remChain`-parameterised predicate; then
  the peel step / base / recursion can be stated at the right generality. This is the multi-module
  mountain.
- The landed `iInf_axisRatio_le_monomialThreshold` is a genuine down-payment on that carrier's terminal
  (piece 6), reusable and S2-free, independent of which carrier is chosen.
