# Statement card — SJState shared-divisor SUPPORT MAP + terminal bridge (STEP-2 carrier, part 1)

Thread `genm-sjcarrier3` (tide, off `origin/genm-sjcarrier2` @ `b05302d5`). Branch `genm-sjcarrier3`.
Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJLedger.lean` (366 LoC, new).
The R1-UPPER final gate → `sjJointResolution` (`RouteMSJResolution.lean:803`), pure R-BLOWUP route.

> **Claim.** The `SJState` recursion carrier's **shared-divisor SUPPORT MAP** — the ledger the
> adjudication (`pure-vs-atom-adj.md` / `chart-lemma-probe.md`, verdict A: the pure R-BLOWUP avoids the
> atom's Gram wall) identified as the load-bearing datum — is defined at general (opaque) generator/
> divisor counts, and the terminal loss it carries lands **EXACTLY** on the banked
> `monomialIntegrand`/`monomialThreshold` finiteness endpoint, with the monomial exponent `k` = the
> support map's shared-divisor exponent `min_i e(i,ℓ)`. The load-bearing shared-vs-fresh distinction
> (DATA-A: `⟨δx,δy⟩` shared `k_δ=1` vs `⟨δ₁x,δ₂y⟩` fresh `k=0`) is proved in-file.

## Lean (all in `DLNFibre.DLN.RLCT`, `RouteMSJLedger.lean`)

- **Carrier defs.** `SJSupport ι d := ι → Fin d → ℕ` (the support map: `e i ℓ` = order to which
  exceptional divisor `u_ℓ` divides generator `bᵢ`); `sharedDivisorExp e ℓ = ⨅ᵢ e(i,ℓ)` (the
  common-divisor exponent, `Finset.univ.inf'`); `genMonomial e i u = ∏_ℓ |u_ℓ|^{e(i,ℓ)}`;
  `commonDivisor e u = ∏_ℓ |u_ℓ|^{sharedDivisorExp e ℓ}`; `residualSupport e i ℓ = e(i,ℓ) − k_ℓ`;
  `sjLoss e u = ∑ᵢ (genMonomial e i u)²`.
- **`sjLoss_factor`** : `sjLoss e u = (commonDivisor e u)² · sjLoss (residualSupport e) u`. The common
  monomial `g` factors out of the sum of squares (exact Nat-power algebra; no division; valid at
  `u_ℓ = 0`).
- **`commonDivisor_sq`** : `(commonDivisor e u)² = ∏_ℓ |u_ℓ|^{2 · sharedDivisorExp e ℓ}` (matches the
  `∏|u_j|^{2k_j}` factor of `monomialIntegrand`).
- **`sjLoss_terminal_integrand`** (the terminal bridge, EXACT) :
  `(sjLoss e u)^{−c'} · (∏_ℓ |u_ℓ|^{h_ℓ}) = monomialIntegrand d (sharedDivisorExp e) h c' u ·
  |sjLoss (residualSupport e) u|^{−c'}`. The ledger's Jacobian-weighted terminal loss IS the banked
  terminal integrand, with `k = sharedDivisorExp e` — the support map's `min_i` output is the `k` of
  the finiteness endpoint.
- **`sjLoss_residual_ge_one`** : a dehomogenised chart generator (`∀ℓ, e i₀ ℓ = k_ℓ`) forces the
  residual unit `≥ 1`; **`sjLoss_residual_le_card`** : on the box (`|u_ℓ| ≤ 1`) the residual unit
  `≤ #generators`. Together: unit `∈ [1, #ι]`, the `[a,b]` the terminal integrability needs.
- **`continuous_sjLoss_residual`** : the residual unit is continuous (⟹ measurable).
- **`sjLoss_terminal_lintegral_lt_top`** : consequently, below `monomialThreshold d (sharedDivisorExp
  e) h` and given a dehomogenised generator, `∫⁻_{unitBox} ofReal((sjLoss e u)^{−c'}·∏|u_ℓ|^{h_ℓ}) < ⊤`.
  Composes the terminal bridge with the banked `terminal_monomial_mul_unit_lintegral_lt_top`
  (`a=1`, `b=#ι`).
- **`dataA_shared_vs_fresh`** (non-vacuity, the load-bearing datum) : `sharedDivisorExp suppShared 0
  = 1` (shared `δ`) with `= 0` off it, and `sharedDivisorExp suppFresh ℓ = 0 ∀ℓ` (fresh). Witnesses
  `suppShared` (`[[1,1,0],[1,0,1]]`), `suppFresh` (`[[1,0,1,0],[0,1,0,1]]`) exhibited in-file.

### The Case-2 generator-level radial step (grounded Phase-2 slice)

- **`prependColumn a e`** : the ledger update of a single radial blow-up — a fresh divisor `u₀` (new
  index `0`) divides `bᵢ` to order `a i`; old divisors shift to `Fin.succ`.
- **`genMonomial_prependColumn`** : `genMonomial (prependColumn a e) i (u₀ ::: u) = |u₀|^{a i} ·
  genMonomial e i u` (the fresh divisor factors out of each generator).
- **`sjLoss_prependColumn_one`** : Case-2 full block (`a ≡ 1`) — `sjLoss (prependColumn (fun _ ↦ 1) e)
  (u₀ ::: u) = u₀² · sjLoss e u`, the GENERATOR-level form of `corankStep`'s `frobSq((u•Δ)·Q) =
  u²·frobSq(Δ·Q)`, with the sharing now recorded.
- **`sharedDivisorExp_prependColumn_one_zero`** : the Case-2 fresh divisor's common-divisor exponent
  `= 1` (fully shared) — the shared-divisor datum `frobSq` cannot see, at the generator level.
- **`sharedDivisorExp_prependColumn_succ`** : old divisors' shared exponents are PRESERVED (the
  passive-prefactor invariant — earlier exceptionals never divided).

## Proved / Assumed / Cited / Deferred

- **Proved.** All the above, sorry-free. Forced `#print axioms` (scratch, force-elaborated):
  `sjLoss_factor`, `sjLoss_terminal_integrand`, `sjLoss_terminal_lintegral_lt_top`,
  `dataA_shared_vs_fresh` all = `[propext, Classical.choice, Quot.sound]` (clean-three). **S2-FREE — no
  `monomial_rlct`** enters (confirmed on the terminal finiteness result, which rides only the banked
  measure bricks).
- **Assumed (carried as hypotheses, not proved here).** The terminal finiteness carries (i) the
  dehomogenised-generator existence `∃ i₀, residual = 0` and (ii) `c' < monomialThreshold d k h`. Both
  are DISCHARGED by the (deferred) relative chart lemma + charge accounting (a chart always dehomogenises
  one generator; the terminal exponent `= Mval ≥ minAdm`, banked `minAdmRec_eq_minAdm`).
- **Cited.** none new. Rides the banked `monomialIntegrand`/`monomialThreshold` (`Skeleton`),
  `terminal_monomial_mul_unit_lintegral_lt_top` (`RouteMSJTerminal`) — all clean-three.
- **Deferred (Phase 2/3 — the remaining mountain, reported precisely).** The **block-elimination
  half** of the `(S,J)` step (the `Z`-independent unit reduction `Case111`/`Case222` at opaque widths,
  at the GENERATOR level — the corank DECREMENT transforming the generators, not merely factoring the
  radial), the Case-1 partial-block merge, the RECURSION down the `(S,J)` profile to this terminal, and
  the measure-theoretic assembly into `gammaPeelIntegral < ⊤`. **`sjJointResolution` UNTOUCHED** (still
  the single named sorry at `RouteMSJResolution.lean:803`).

## The precise remaining step (Phase 2 — the hardest bounded brick)

Decorrelated Codex (this thread, xhigh, `codex/carrier-design-{prompt,answer}.md`) confirmed the
encoding and named the sharp risk: **the banked frobSq-level bricks (`corankStep_prefactor`:
`pref·frobSq = pref·u²·residual`, `RouteMSJCorankStep`) are TOO COARSE to recover the support matrix.**
A sum-of-squares (`frobSq`) equality does NOT certify which generators share a divisor `u`;
shared-divisor faithfulness must be tracked **generator-by-generator**.

- **DONE this tide (the radial-factor sub-step):** `prependColumn` + `sjLoss_prependColumn_one` +
  `sharedDivisorExp_prependColumn_{one_zero,succ}` are exactly that generator-level step FOR THE RADIAL
  FACTOR — the fresh `u₀` shared across all generators gives `u₀²`, sharing recorded, old columns
  preserved. This is the ledger-update shape Codex asked for, for the radial half.
- **REMAINING (the block-elimination half):** the generator MAP under the `Z`-independent unit
  reduction — how the corank block's Plücker/generator coordinates transform when `Case111`/`Case222`'s
  det-1 row/col transforms reduce `D_J → [[1,O],[O,D_{J+1}]]` at opaque widths. This is the corank
  DECREMENT (new generators from the Schur-reduced block), NOT the radial factor. Then: the `(S,J)`
  RECURSION driving the ledger down to the terminal (`sjLoss_terminal_lintegral_lt_top`), and the
  measure assembly bounding `gammaPeelIntegral` by the finite sum over charts of these terminal
  integrals (via banked `pivotChartCover_matBox_le_sum` / `radial_morse_residual_power_le`). Lifting
  `Case111`/`Case222` at the GENERATOR level (not `frobSq`) is the true test.

## Status

sorry-free; clean-three; `scripts/sorries` = 0 for the module; full aggregator NOT yet wired
(`DLNFibre.lean` is single-writer — controller to add `import DLNFibre.DLN.RLCT.Validate.RouteMSJLedger`
at the end). No name clashes with siblings (`rg`-checked). Isolated `scripts/lb
DLNFibre.DLN.RLCT.Validate.RouteMSJLedger` green (2709 jobs). 379 LoC.

**Reviewer: SURVIVED** (independent fidelity + soundness audit, decorrelated Codex xhigh corroborated
Q1 faithfulness + Q5 overclaim). All six checks pass: `sharedDivisorExp = ⨅ᵢ` faithful (monomial-gcd,
not pairwise); terminal bridge EXACT with `k = sharedDivisorExp` (not `2k`); H1/H2 hypotheses honest
(satisfiable, not vacuous, not hiding the hard part); Case-2 step matches `frobSq_smul_mul`'s `u²`;
scope honest (`sjJointResolution` untouched); forced-recompile `#print axioms` clean-three, no
`monomial_rlct`/`sorryAx`. Two LOW observations, both addressed: (1) added the in-file H1-path witness
`suppDehom = [[1,0],[1,1]]` + its `∃ i₀` example (the finiteness hypothesis is genuinely satisfiable);
(2) the DATA-A RLCT values (½ / 1) are cited-motivation (attributed to DATA-A), not in-file theorems —
the module proves only the `k`-exponents, correctly.
