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

## The spine risk (top watch)

`aoyagiλ` is `min over Adm`, a cone reconstructed from p.22 and verified numerically (437/437) but NOT
proved to equal the exponents R1's resolution literally produces. `Adm = R1-exponents` is the
load-bearing equality; the headline is honest only once it's proved. Settled by the validate-small-first
gate (build R1's smallest charts, read literal exponents, confirm =Adm). pp's flag 3.

## Topology note

Controller session is in worktree `rung0-defs` (branch worktree-rung0-defs); main checkout holds the
canonical `expedition/aoyagi-full`; both at same HEAD. Teammate isolation-worktrees collapse onto
rung0-defs ⇒ serial teammates. Editing happens in rung0-defs; controller merges →expedition/aoyagi-full
in main + pushes. For the parallel middle phase, recommend operator relaunch controller from main
checkout (non-blocking; re-ground from docs).

## What's done / banked

- Setup + Rung 0 design (this + prior tick). Design merged (25b825b), pushed.

## Next tick

Spawn Rung 0b (formaliser, serial, in rung0-defs with symlinked .lake/packages): encode Foundations +
skeleton. Then Rung 0c (hardener+reviewer on encoded Lean) gates before S1/L1/… On 0b+0c clear, open the
small-case validation thread (the gate + spine-risk probe) and the tractable L1/L2/A1 in sequence.
