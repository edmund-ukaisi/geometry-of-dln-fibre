# Controller loop — rlct-bridge  ·  ARCHIVE (expedition CLOSED 2026-06-28)

> **This expedition is COMPLETE. This file is an archival note, not an active controller prompt** — it no
> longer carries live Tick/Wake/delegation instructions. If the PR reopens work or a follow-up expedition
> starts, write a fresh loop-prompt.

## What it achieved (the programme's prize)

Made `rlct(K^DLN_B) = ½·C` honest in Lean. The monolithic Cited axiom `RlctInterface.cited_aoyagi_dln`
is retired; the payoff now rests on **exactly two cited facts, both irreducibly analytic — Watanabe `≤`
and Aoyagi `≥`** — with EVERY codimension fact, **including the real↔complex transfer**, PROVED.

- **Phase 1:** monolith → thin `RlctRealInterface` (opaque `rlct` + the two analytic bounds) + the
  connector + `codim_K = C` + projection-compatibility (closed the prior fibration-geometry residual).
- **Phase 2:** the transfer `hT` (`codim_ℝ = codim_K`) is now the THEOREM
  `DLN.codimRealFibre_eq_codimRepCanonical_baseChange` (both sides = the field-independent `C+δ`),
  discharged from all 8 payoffs. The "real-AG library" turned out to be a vestigial
  `[IsAlgClosed]→[CharZero][Infinite]` typeclass relaxation of the repo's own field-generic orbit-dim
  squeeze (ℝ satisfies it) — NOT a from-scratch IFT/semialgebraic-dimension build.

Green throughout (3818 jobs), sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`; every
stage twice-decorrelated-reviewed (fidelity + hardener). **PR #13** is the well-rounded Phase-1+2 final;
review/merge + the `dev → master` promotion are operator-gated.

## Disposition that drove it (kept for reuse)
Hold the vision; let the sea rise (no-Mathlib-support ≠ blocker — build the geometry, cite the analytic
core); be more ambitious than the teammates; bedrock + name=content (no `rlct_…` that secretly assumes the
interface); decorrelated-review the crux; L3 sweep-the-semantic-class to empty on any framing fix; blind to
the parallel aoyagi `RLCT/*` line (decorrelation).

## Roadmap residuals (future expeditions — NOT needed for this result)
Global `Flat π` / fibre bundle over `rankROpen` (target-side cocycle; Mathlib `AlgEquiv` gaps); the
fibre-component / LR-Lemma-4.6 `[IsAlgClosed]` layer (a "full-relaxation" follow-up); the cross-paper fold
to aoyagi-full's genuine `rlctAt` via the field-free `aoyagiLambda ↔ Aoyagi.lambda` identity.

Full account: `synthesis.md` (§ PHASE 2 CLOSED) · lessons: `lessons.md` (L0–L9) · threads: `threads.md`.
