# genm-decrecon — recon-map: the DECORATED (S,J) recursion route → close `sjJointResolution:803`

**Seat:** self-recon (read-only). **Date:** 2026-07-10. **Base:** `expedition/aoyagi-full` @ `57ea5c36`.
**Charge:** map the banked decorated-(S,J) machinery for the upcoming `decorated_peel_step` build; confirm
sole-gap status or enumerate the full gap list; verdict on integrating `origin/genm-covfinish` transport.
**No Lean edits, no builds.**

---

## HEADLINE (fold into the tide spec)

The controller's premise needs one correction and one refinement.

**Correction.** `decorated_peel_step` is **NOT a stated Lean contract**. It appears ONLY in prose /
docstrings (`RouteMSJDecorated:40`, `RouteMSJDecoratedRowMix:6/36`, `RouteMSJDecoratedCharge:25`,
`RouteMSJDecoratedRadial`, the `DLNFibre.lean` + `AxCheck.lean` comment log). There is **no
`def`/`theorem`/`axiom`/hypothesis binder** named `decorated_peel_step` anywhere in the tree (verified
by `rg`), and **no conditional recursion theorem takes it as a hypothesis**. So "the recursion is proved
CONDITIONAL on `decorated_peel_step`" is not literally true — the conditional recursion does not yet
exist as a Lean object. `origin/genm-covfinish`'s own `notes.md` agrees: it calls `decorated_peel_step`
"**named, unbuilt**".

**Refinement — the sole-gap status.** `decorated_peel_step` is the sole unbuilt *analytic* content, but
it is **not the sole unbuilt piece**. Reaching `DecoratedBoxThresholdFinite (trivial M) ∀M` (the thing
the banked bridge turns into `RouteMBoxThresholdFinite M`) needs **three** unbuilt pieces:

- **GAP 1 — the peel step** (`decorated_peel_step`, the analytic CoV): unstated, unproved. Reduces the
  decorated predicate at `redChain u M` (shifted threshold) to the parent at `M`.
- **GAP 2 — the well-founded recursion DRIVER**: unstated, unproved. The analog of the banked
  `routeMBoxThresholdFinite_of_step` — strong induction on chain arity chaining GAP 1 from `trivial M`
  to the terminal. Structural/cheap, but **not written** (unlike the gammaPeel route, whose wrapper IS
  built).
- **GAP 3 — the terminal base wiring**: connecting the fully-resolved leaf's `SJDecoration.integral` to
  the banked `sjLoss_terminal_lintegral_lt_top`. The terminal lemma is banked; the wiring is not.

**What to reuse:** the ENCODING is fully banked and validated (predicate + trivial recovery + radial
sub-brick both pointwise & integral-level + rowMix (a)-half at fresh block + measurability + terminal
finiteness + the threshold-shift soundness cast). **What's staged:** `carrierThreshold_shift`,
`radialAttach_integral`, `rowMix_decLoss`, `sjLoss_terminal_lintegral_lt_top` exist precisely for this
point. **What to avoid:** the bare-inequality contract (circular), the box-Morse/GMT route (retired),
the naive-fibre route (loses threshold), the good-branch-only close (dimensionally partial), and the
det(Q_bQ_bᵀ) Gram FIELD (the atom trap).

**Crucial framing nuance.** The decorated route does **not "close 803"** in the sense of filling that
sorry with the recursion. It proves `RouteMBoxThresholdFinite M ∀M` **independently**, making the whole
gammaPeel route (`sjJointResolution` + `sjResolutionStep_proof` + `routeMBoxThresholdFinite_sjResolution`)
**obsolete**. 803 can be retro-filled via the banked `sjJointResolution_of_boxThresholdFinite` bridge for
tidiness, but the capstone consumers want `RouteMBoxThresholdFinite M ∀M`, delivered by
`decoratedBoxThresholdFinite_trivial_iff ∘ (decorated recursion)`.

---

## Q1 — `decorated_peel_step`: exact declaration

**NONE — it is prose, not a declaration.** Not a `def : Prop`, not a hypothesis binder, not an `axiom`,
not a `theorem`. Consumed nowhere as a Lean object. It names, in the design docstrings, the target
composition **(a) rowMix scalar Schur elim + (b) radialAttach + (c) block-split regime A/B (incl. the
`c'=pq/2` boundary)** = one single decorated peel.

---

## Q2 — the conditional chain + FULL gap enumeration

### The bridge chain (real, sorry-free, clean-three — MODULO the decorated recursion)

1. `decoratedBoxThresholdFinite_trivial_iff M` — **`RouteMSJDecorated:217`, PROVED.**
   `DecoratedBoxThresholdFinite (trivial M) ↔ RouteMBoxThresholdFinite M`. (`carrierThreshold M =
   ½·minAdm M`; integrals coincide via `trivial_integral_eq`.)
2. `sjJointResolution_of_boxThresholdFinite M hM t ρ κ c' hc'` — **`RouteMSJJointReduce:68`, PROVED.**
   GIVEN `hM : RouteMBoxThresholdFinite M`, delivers `gammaPeelIntegral M t ρ κ c' < ⊤` = the exact goal
   at `RouteMSJResolution:803`. Uses `gammaPeelIntegral_le_boxIntegral` (`JointReduce:53`, PROVED — pure
   `lintegral_mono_set` over `routeMLayerBoxIntegral_front_split`; does NOT use the per-chart `hIH`).

So: `DecoratedBoxThresholdFinite (trivial M)` →(1) `RouteMBoxThresholdFinite M` →(2) close 803. **Both
links (1),(2) are built sorry-free.** The gap is entirely UPSTREAM of `DecoratedBoxThresholdFinite (trivial M)`.

### Other unbuilt pieces in the chain — enumerated (the crux)

`decorated_peel_step` is **NOT genuinely sole**. Between the banked encoding and
`DecoratedBoxThresholdFinite (trivial M) ∀M` there are three unbuilt pieces, GAP 1/2/3 above. GAP 1 is
the analytic heart; GAP 2 and GAP 3 are structural and cheaper but not yet written.

### No circularity (why the decorated route is legitimate)

Closing 803 via link (2) needs `RouteMBoxThresholdFinite M` for the *same* M — which the decorated
recursion proves by a well-founded induction on *chain arity / decoration complexity* (via `redChain u M`
strictly shorter), NOT through `sjJointResolution`. Self-contained; no cycle. (Contrast the bare-inequality
contract, which IS circular — Q5.)

### Cross-check: the SOLE live R1-UPPER sorry is 803; a stale docstring

`routeMBoxThresholdFinite_sjResolution` (`RouteMSJResolution:951`) already asserts
`∀M, RouteMBoxThresholdFinite M`, gated only on `sjResolutionStep_proof` → `sjJointResolution:803`.
**`sjBoundaryPeel` (`RouteMSJResolution:688`) is CLOSED** (no live sorry in its body, 688–761) and
`sjBase1_freeMatrix` (`:912`) is CLOSED. So **803 is the sole live sorry** in the whole
`RouteMBoxThresholdFinite` chain. ⚠️ The `:951` docstring ("Carries exactly the two remaining ... sorries:
`sjBoundaryPeel` ... and `sjJointResolution`") is **STALE** — `sjBoundaryPeel` no longer has a sorry.

---

## Q3 — what `decorated_peel_step`'s proof needs (each piece verified)

| Sub-part | Status | Where / name |
|---|---|---|
| **(a) clear-first rowMix Schur elim — algebraic identity (fresh block)** | **BUILT, sorry-free** | `SJDecoration.rowMix` (`RowMix:56`), `SJDecoration.rowMix_decLoss` (`RowMix:100`, mixed quadratic form `∑ⱼ(∑ᵢRⱼᵢgenᵢ)²`, unconditional at CONSTANT support via `hconst`), `rowMix_d/jac/dom` invariants |
| **(a′) support-homogeneity `hsh` for the ACTUAL analytic Schur matrix `R=P⁻¹B` at a NON-fresh block** | **UNBUILT** | RowMix docstring explicitly defers this "synchronisation" to the recursion. (a) is only half-built: identity yes, analytic-`R` application no |
| **(b) radialAttach** | **BUILT, sorry-free, clean-three** | `SJDecoration.radialAttach` (`RouteMSJDecorated:242`), `radialAttach_decLoss` (`:262`, `u₀²` factor); integral-level `SJDecoration.radialAttach_integral` (`Radial:83`, factoring UNCONDITIONAL in `c'`) + `radialAttachFactor_lt_top` (`Radial:65`, per-divisor Morse threshold `c'<(j₀+1)/2`) |
| **(c) block-split regime A/B incl. `c'=pq/2` boundary ε-argument** | **UNBUILT** | Not a Lean object anywhere — prose only (`RouteMSJDecorated:40`, covfinish notes). The genuinely-new content. `c'=pq/2` = the log-borderline, correctly excluded by strict `c'<½minAdm` (exponents-cert §2d) |
| landing on `redChain u M` at threshold shifted `½·peelCharge` (`carrierThreshold_shift`) | **BANKED** | `carrierThreshold_shift` (`RouteMSJDecorated:71`) = `half_minAdm_sub_half_peelCharge_le` (`Charge:52`, cast of `minAdm_le_peelCharge_add_redChain` `Charge:37`; soundness `0/171`). Non-vacuity: `exists_binding_cut` (`Charge`) |
| well-founded recursion to terminal | **DRIVER UNBUILT (GAP 2)**; terminal lemma **BANKED** | Terminal: `terminal_monomial_mul_unit_lintegral_lt_top` (`RouteMSJTerminal:160`), `sjLoss_terminal_lintegral_lt_top` (`RouteMSJLedger:234`). The driver chaining peels to them is not written |
| measurability plumbing for the factoring (Tonelli / `lintegral_const_mul`) | **BANKED** | `RouteMSJDecoratedMeas`: `measurable_decLoss`, `measurable_decLoss_uncurry`, `measurable_integrand`, `continuous_jacMonomial`, `decLoss_nonneg`; carrier's `residualMeas` field |

Net: (b) fully banked; (a) half-banked (algebra yes, analytic-`R` synchronisation no); (c) unbuilt;
threshold-shift + terminal-finiteness + measurability banked; the recursion driver unbuilt.

---

## Q4 — route reuse: integrate covfinish's transport modules?

**Verdict: the decorated `decorated_peel_step` route is LARGELY INDEPENDENT of the ~15 endpoint/good-chart
modules.** The decorated peel composes rowMix (a) + radialAttach (b) + block-split (c) + the decoration
ledger, all at the **carrier (`SJLinGenState`) level** — not the matrix-box `sjGoodChartLoss`/`sjGoodMap`
endpoint level. Those endpoint modules (`sjGoodMap_loss_matBox_lt_top` `GoodChart:269`,
`corner_block_lt_top_of_pos`, VExpose, GoodCoords, DepthReduce, SphereLB) belong to the ENDPOINT /
GOOD-BRANCH route, which covfinish's own verdict shows closes ONLY the dimensionally-cooperative branch
(needs `W`, `A₂` both right-invertible — impossible when `M₁−t>M₂` or `M₂>M_last`). The deeper
(rank-deficient) branch IS the decorated recursion.

**On `origin/genm-covfinish` specifically** (2 new Lean modules, 198 lines, both clean-three, verified
sorry-free by reading; base `5d276748`, one commit behind our `57ea5c36`):
- `RouteMSJTransport.gammaPeelIntegral_piSplit_eq` (`:` — pure `lintegral_congr` MP Pi-split): rewrites
  `gammaPeelIntegral` splitting `A'` into leading layer `p.1 : M₁×M₂` + deeper `p.2`, deep factor
  `= sjDeepFactorCore M p.2` (`A'0`-independent), front factor `= p.1.submatrix (blockSplitEquiv κ) id`.
- `RouteMSJRowSplit.rowSplit_lintegral_eq` (+ `rowSplitEquiv`, `measurePreserving_rowSplitEquiv`,
  `rowSplitEquiv_reindex/preimage_box`): splits the leading layer into pivot rows `Upiv : t×M₂` + corank
  rows `W : (M₁−t)×M₂`.

**Recommendation: integrate these two as OPTIONAL PLUMBING, not as analytic content.** The Pi-split
`p.1` (leading layer) vs `p.2` (deeper) is exactly the coordinate frame the decorated peel operates in —
rowMix (a) acts on `p.1`'s rows; the deeper `p.2` is the decoration's `Z`-domain. They are clean-three
and low-risk. They do NOT reduce GAP 1/2/3. **Deprioritize** the full good-branch assembly (bounded
plumbing that closes only the wrong branch). If integrating: rebase covfinish's 2 modules onto the
canonical tip (trivial — they're additive, base is one commit back).

---

## Q5 — lessons / dead-ends to carry into the spec

### DO
- **Structure the peel as a decoration→decoration CoV**, never a bare inequality. The bare-inequality
  contract `gammaPeelIntegral ≤ ∑ᵢCᵢ·routeMLayerBoxIntegral(M'ᵢ)` (shorter `M'ᵢ`) is **CIRCULAR**: pick
  `Cᵢ = gammaPeelIntegral / routeMLayerBoxIntegral(M'ᵢ)` (finite, positive) and it's EQUIVALENT to
  `gammaPeelIntegral<⊤` — zero reduction content (covfinish notes). This is *why* `SJDecoration` exists.
- **ABSORB the Gram weight `det(Q_bQ_bᵀ)^{−(M₀−t)/2}` into the decoration's shared-divisor support** —
  never materialise it as a detached weight. That is the design point of the `SJLinGenState` carrier.
- **Exponent bookkeeping** (`threads/genm-covdesign/sjjoint-exponents-cert.md` §2, and the covdesign
  cert Q5 target): per level `θ_true(q) = max{0, 2c'−m₀(q−1)}`; `D_q = cCodim (tailChain M) (q−1)`
  [BANKED, RlctPayoffGeneral Brick A]; linchpin `minAdm M ≤ D_q + m₀(q−1)` [banked precedent
  `minAdm_rrp_subadd`, `RouteMSchurThresholdP:106`]; target is **integrability** (`θ_true<D_q` strict for
  `c'<½minAdm`; `θ=D` log-borderline at `c'=½minAdm`, correctly excluded). Per-peel: `c'` shifts by
  `½·peelCharge`, `peelCharge M u = (M₀−u)(M₁−u)` (`Charge:33`).

### AVOID (refuted routes)
- **Box-Morse / front-peel route — RETIRED** (exponents-cert §1, triple-confirmed me/forkreview/neutral
  Codex): brick (ii) needs a real-tube/sublevel bound (`vol{σ_min(Q_b)≤t}≲t^D`) that requires GMT
  (Łojasiewicz / coarea / Weyl tube / Hironaka) **absent from Mathlib v4.29** (only `Layercake`). The
  algebraic `cCodim` = `Ideal.height` does not bridge to a Lebesgue tube exponent. (S,J) does the flag
  directly — it CONSTRUCTS the normal-crossings resolution that box-Morse would have to import.
- **Naive fibre route** (bound pivot chart by full box + `fibre_lintegral_mul_le`): caps at `c'<M₀/2`,
  but `minAdm>M₀` in 417 of the L=3..5 width-≤4 chains → loses threshold room. The pivot chart is
  essential (covfinish finding 1).
- **Good/endpoint branch alone does NOT close (□)**: requires `W` and `A₂` both right-invertible —
  dimensionally impossible when `M₁−t>M₂` or `M₂>M_last`, positive-measure rank-deficient otherwise
  (covfinish finding 2; the controller's own note).
- **`hIH` on `redChain`/`tailChain` as a black box does NOT close the deeper branch**: the Gram weight
  blows up on the rank-deficient locus, and at the binding cut `minAdm M = a + minAdm(redChain t* M)`
  the residual exponent EXACTLY saturates the reduced-chain IH threshold — Hölder-infeasible (FreedPeel
  header + covfinish finding 3 + genm-sjjoint-design cert). The decoration's shared-divisor absorption is
  the way past this.
- **det(Q_bQ_bᵀ) Gram FIELD as a decoration field — the "atom trap"**, explicitly rejected in
  `RouteMSJDecorated` (a scalar `diag(b)` weight cannot express `min_i` over `supp`; RouteMSJLedger DATA-A).

### Prior tide notes on the peel / rowMix
- `genm-sjbuild3` → `RouteMSJDecoratedRowMix` (the (a)-half, fresh-block only; `hsh` for analytic `R`
  deferred).
- `genm-sjassembly` → `RouteMSJDecoratedRadial` / `Meas` (the (b) radial integral factoring + carrier
  measurability field).
- `genm-sjnative` → `RouteMSJDecoratedCharge` (the threshold-monotonicity soundness cast).
- `genm-r1predicate` / `genm-r1decorated` / `genm-sjcarrier4` → the design certs pinning the predicate
  (`carrierThreshold = Θ(M,π)`, 3592/3592; the CoV as ~65–75% genuinely-new).

---

## Proposed tile decomposition (what a formaliser tide should build, in order)

- **Tile 0 (structural, cheap — DO FIRST): make the conditional chain real.** STATE `decorated_peel_step`
  as a Lean `Prop` (the single-peel reduction: `DecoratedBoxThresholdFinite (reduced decoration on
  redChain u M)` → `DecoratedBoxThresholdFinite (D on M)`, at threshold shifted by `½·peelCharge`), AND
  STATE the well-founded driver `∀M, DecoratedBoxThresholdFinite (trivial M)` conditional on it (GAP 2,
  the analog of `routeMBoxThresholdFinite_of_step`). Compose with `decoratedBoxThresholdFinite_trivial_iff`
  + `sjJointResolution_of_boxThresholdFinite` so that, MODULO the stated peel step, 803 closes. This turns
  the controller's framing ("conditional on `decorated_peel_step`") into fact — currently it is only prose.
- **Tile 1 (plumbing): the block-split coordinate frame.** Integrate/adapt covfinish's
  `gammaPeelIntegral_piSplit_eq` (leading layer `p.1` vs deeper `p.2`) + `rowSplit_lintegral_eq` (pivot
  rows `Upiv` vs corank rows `W`). This is the frame the peel operates in.
- **Tile 2 (a′): analytic-`R` rowMix.** Discharge `rowMix`'s `hsh` support-homogeneity for the real Schur
  matrix `R = P⁻¹B` (invSchurLeft/invSchurRight) at the non-fresh block; wire `rowMix_decLoss` into the
  peeled integrand.
- **Tile 3 (b): radial — mostly wiring.** `radialAttach_integral` + `radialAttachFactor_lt_top` are
  banked; connect the `u₀²` factor + `carrierThreshold_shift`.
- **Tile 4 (c): block-split regime A/B + `c'=pq/2` boundary.** The genuinely-new content. Regime A
  (`c'>pq/2`): radial peel + reduced decoration. Regime B (`c'≤pq/2`): the bounded/core-positive branch
  (cf. the `freedSchurLoss_inner_bounded_lt_top` pattern in `RouteMSJFreedPeel`). Boundary `c'=pq/2`:
  log-borderline, excluded by strict `c'<½minAdm`.
- **Tile 5 (GAP 3): terminal wiring.** Connect the fully-resolved leaf decoration's `SJDecoration.integral`
  to `sjLoss_terminal_lintegral_lt_top` (`Ledger:234`, banked).

---

## Reflection (self-recon)

- **Most likely to advance:** Tile 0. Making `decorated_peel_step` + the driver into actual stated Lean
  objects (conditional on the analytic step) would convert the entire framing from prose to a proved
  conditional, isolate the true remaining analytic gap to Tile 4(c) alone, and let the controller spec a
  crisp "prove this one Prop" tide. It is cheap and de-risks everything downstream.
- **Most likely to break:** Tile 4(c), the block-split regime A/B with the `c'=pq/2` boundary — the only
  genuinely-new analytic content, and the point every prior tide and both Codex passes flag as the ~65–75%
  novel construction. The regime-B/borderline ε-argument is where an over-clean statement will hide a hole.
- **Next computation to clarify:** write out (pen-and-paper) the exact statement of ONE `decorated_peel_step`
  on the smallest genuinely-3-layer bottleneck (`(3,3,4)` or `(1,2,2)` where `minAdm>M₀`), tracking the
  decoration `(d, jac, carrier)` before/after and checking the shifted threshold `carrierThreshold M −
  ½·peelCharge ≤ carrierThreshold (redChain u M)` numerically against the exponents-cert `θ_true<D`
  target. If the decoration bookkeeping closes on that instance, Tile 0's statement is well-posed.
