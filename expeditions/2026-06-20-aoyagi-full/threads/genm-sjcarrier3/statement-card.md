# Statement card — SJState shared-divisor SUPPORT MAP + terminal bridge (STEP-2 carrier, part 1)

Thread `genm-sjcarrier3` (tide, off `origin/genm-sjcarrier2` @ `b05302d5`). Branch `genm-sjcarrier3`.
Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJLedger.lean` (291 LoC, new).
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
- **Deferred (Phase 2/3 — the remaining mountain, reported precisely).** The **relative corank-step
  invariant** at opaque widths: the pointwise `(S,J)` step that PRODUCES this support map from the raw
  loss (blow up one radial, `Z`-independent unit block-elimination, append the fresh divisor column to
  the ledger, preserving the passive-prefactor invariant), its recursion to this terminal, and the
  measure-theoretic assembly into `gammaPeelIntegral < ⊤`. **`sjJointResolution` UNTOUCHED** (still the
  single named sorry at `RouteMSJResolution.lean:803`).

## The precise remaining step (Phase 2 — the hardest bounded brick)

Decorrelated Codex (this thread, xhigh, `codex/carrier-design-{prompt,answer}.md`) confirmed the
encoding and named the sharp risk: **the banked frobSq-level bricks (`corankStep_prefactor`:
`pref·frobSq = pref·u²·residual`, `RouteMSJCorankStep`) are TOO COARSE to recover the support matrix.**
A sum-of-squares (`frobSq`) equality does NOT certify which generators share a divisor `u`;
shared-divisor faithfulness must be tracked **generator-by-generator**. So Phase 2 must build a
GENERATOR-LEVEL step lemma (shape, per Codex): a computable `radialUpdate : SJState → StepData →
SJState` whose support copies old columns monotonically (old exponents never decrease — the
passive-prefactor invariant) and appends exactly one fresh divisor column (the blown-up radial),
asserting `loss_after = ∑ᵢ (genMonomial state'.support i u')²` with the recursion measure decreasing.
Lifting `Case111`/`Case222` (the `(2,2,2)` block-elimination templates) to opaque widths at the
GENERATOR level — not the `frobSq` level — is the true test.

## Status

sorry-free; clean-three; `scripts/sorries` = 0 for the module; full aggregator NOT yet wired
(`DLNFibre.lean` is single-writer — controller to add `import DLNFibre.DLN.RLCT.Validate.RouteMSJLedger`
at the end). No name clashes with siblings (`rg`-checked). Isolated `scripts/lb
DLNFibre.DLN.RLCT.Validate.RouteMSJLedger` green (2709 jobs). Awaiting reviewer fidelity check.
