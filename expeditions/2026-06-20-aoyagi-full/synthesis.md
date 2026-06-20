# synthesis.md — Aoyagi-Full controller's integrative read

(Internal ledger; assumes repo context. Flushed every tick; read on re-ground. Not a deliverable.)

## Current read (2026-06-20, after Rung 0 design)

Rung 0 design landed (`threads/01-…/design-spec.md`, 479 lines, merged to expedition/aoyagi-full).
Controller-reviewed + Codex-decorrelated-audited as **bedrock-quality and faithful**. The foundation:

- `dlnLoss = ‖prod·−B‖²_F`; `optimalSet = fibre`; Σ_X drops out via S1.
- `rlctAt = sSup{ c | ∃U∈𝓝w*, IntegrableOn |F|^(−c) U }` in ℝ≥0∞ — faithful Aoyagi Def 1 (bump removed
  via existential-nbhd sandwich = φ-independence). Precondition: F real-analytic, ≢0 near w* (dlnLoss is
  polynomial ⇒ OK). Pole-sign: largest pole at z=−λ.
- `aoyagiλ = reg + ½·min_{T∈Adm} M(T)` — TOTAL (Finset.inf' over finite Adm, T=0 always admissible),
  Def-3-free. Clean form `¼(Σqᵢ²−Σmₖ²)` (q=balanced ℓ-split) is its *value* at the minimiser (A1);
  printed Theorem-2 = clean where Def 3 applies (verified symbolically). NOT an ℓ-extremisation (both
  naive readings wrong: max-over-ℓ ≠ Def-3; min-over-ℓ negative).
- `rlctOrderAt` (θ): analytic pole order; combinatorial `aoyagiθ=a(ℓ−a)+1` is the deliverable; the
  analytic=chart-count equality rides inside S2. Secondary.
- **S2 (the one axiom):** chart-level normal-crossing→(λ,θ); minimal hypotheses pinned (cover, proper
  charts, monomial pullback + monomial Jacobian with |·|, units bounded away from 0). Irreducible cited
  fact = `∫₀^ε u^{h−2kc} < ∞ ⟺ c<(h+1)/(2k)`. Cover + change-of-variables + properness stay on our side.
- Goal skeleton (§8): every named statement S1/L1/L2/D1/R1/A1/A2/T as a named sorry + the one axiom.

## The spine risk — RESOLVED into a weaker, cleaner obligation (thread 03)

pp's small-case probe (+ decorrelated Codex) settled it: the set-equality "R1's chart exponents = Adm"
is **FALSE** (charts outnumber T-vectors), but the **value-match** holds on (1,1,1)/(2,1,2)/(2,2,2):
resolution's min chart-ratio `= ½·min_{T∈Adm} Mval(T) = λ_core`. Interpretation: `T` ↔ rank-incidence
stratum, `Mval(T) = codim` (proven L=2) ⇒ `λ_core = ½·min_strata codim`. So `Adm` is the right
*definition* substrate; the R1 obligation shrinks from a set bijection to the **value-match**
(Theorem 3 + resolution existence) — far cleaner, and possibly a cleaner R1 architecture
(`½·min_strata codim`) than chart enumeration. The spine is SOUND. (design-spec §9.3 amended.)

**New top-open item:** the general-L `Mval = codim(nested-rank stratum)` (L=2 verified; L≥3 = the
nested-rank version, not yet proven). pp is on `(2,2,2,2)` to pin it + the divisor-type↔T count (θ).

## Topology note

Controller session is in worktree `rung0-defs` (branch worktree-rung0-defs); main checkout holds the
canonical `expedition/aoyagi-full`; both at same HEAD. Teammate isolation-worktrees collapse onto
rung0-defs ⇒ serial teammates. Editing happens in rung0-defs; controller merges →expedition/aoyagi-full
in main + pushes. For the parallel middle phase, recommend operator relaunch controller from main
checkout (non-blocking; re-ground from docs).

## What's done / banked

- Setup + Rung 0 design (this + prior tick). Design merged (25b825b), pushed.

## In flight (parallel)

- `fm` — Rung 0b encode (shared worktree). Awaiting report.
- `pp` — thread 03 round 2: L=3 `(2,2,2,2)` nested-rank `Mval=codim` + θ divisor-type count. Read-only.

## Next tick

On `fm`'s report: precision/bedrock review of the encoded Foundations + skeleton (Rung 0c, hardener+rv);
ensure the R1 skeleton statement is the **value-match** form (not the superseded set-bijection). On
`pp`'s L=3 report: if `Mval=codim` generalizes, the spine is fully understood → the validate-small-first
Lean gate can start at (1,1,1) (cleanest: no blow-up), then L1/L2/A1. Consider the `½·min_strata codim`
reframing as the R1 architecture.
