# synthesis.md — Aoyagi-Full controller's integrative read

(Internal ledger; assumes repo context. Flushed every tick; read on re-ground. Not a deliverable.)

## Current read (2026-06-20, setup)

Expedition launched. Branch `expedition/aoyagi-full` off `dev`, controller in main checkout,
namespace `DLNFibre.DLN.RLCT.*`. The quest: prove `aoyagi_learning_coefficient` (global RLCT of the
DLN square-Frobenius loss = Aoyagi's closed form), citing only the normal-crossing→RLCT extraction.

**Architecture is settled** (see `brief.md`): the layered skeleton (S0 defs → S1 ideal-invariance →
[S2 cited] → L1/L2 linear algebra → D1 deepest point → R1 resolution → A1/A2 arithmetic → T assemble).
The trusted spine is our own verified results: the clean closed form `2λ_core = ½(Σqᵢ²−Σmₖ²)`, the
Case-2 non-binding lemma, and ground-truth λ/θ for small cases.

**The shape of the work.** Tractable: definitions(plumbing)/L1/L2/A1/A2. Hard/novel:
- the **rlct definition** itself (analytic, build from scratch on Mathlib measure theory);
- **D1** (Theorem 4, second paper — analytic RLCT comparison);
- **R1** the resolution (the mountain — explicit coordinate charts, pullback/Jacobian/coverage).
The cited line is at S2 only.

**First move (Rung 0):** controller architects the precise mathematical content of the four
definitions here + in the brief, then delegates Lean encoding of the skeleton; independent fidelity
review against ground truth before anything stands on them.

## Open questions / drift-guard

- Is `rlctAt` best as `sup{c | ∫|F|^{-c}φ<∞}` (Def 1) or via the zeta function's largest pole? Both in
  Aoyagi Def 1; pick the one that (a) is faithful and (b) feeds the S2 citation cleanly. Likely: define
  via the integral-convergence sup; state S2 as "monomial chart cover ⇒ this sup = min(h+1)/2k".
- θ analytic definition (pole order) — secondary; may land combinatorial θ + flag the seam.
- Does the global infimum over `optimalSet` reduce to the single deepest point? That reduction IS D1
  (Theorem 4). The headline `⨅ w ∈ optimalSet` is faithful *because* D1 is in scope.

## What's done / banked

- Setup: branch `expedition/aoyagi-full` off dev, controller in main checkout, baseRef=head, namespace
  `DLNFibre.DLN.RLCT.*`. Brief + priorities + threads + lessons + loop-prompt written, committed, pushed
  (HEAD 227511c). Task ladder created (#1–#10). Aoyagi 2013 PDF added (D1 source).
- Thread 01 (Rung 0, seat `pp`) **spawned and running in background** (worktree, off HEAD): designing
  the foundational definitions (`rlctAt`/`rlctOrderAt`/`dlnLoss`/`aoyagiλ`), the S2 cited interface, and
  the named-sorry goal skeleton; cross-checking `aoyagiλ` vs ground truth; pinning the Def-3 regime;
  decorrelated Codex on definitional faithfulness. Output: `threads/01-…/design-spec.md` (it commits to
  its worktree branch; controller merges).

## Next tick (on pp's report)

Review the design-spec for fidelity (name=content; faithful to Aoyagi Def 1; ground-truth table holds;
Def-3 regime pinned). If solid → merge it, then spawn Rung 0b (formaliser: encode `Foundations.*` +
goal skeleton, small modular files). If the rlct/θ definition has an infidelity flag, spawn a hardener
decorrelated pass before any encoding. Then begin the small-case validation thread (the anti-treadmill
gate) in parallel with L1/L2 (tractable linear algebra).
