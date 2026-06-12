# synthesis.md — controller's integrative read (core-quiver-engine)

The controller's *internal* integrative ground, flushed every tick (recovery substrate).

## State (after tick 2 + audit)

- **Branch:** `expedition/core-quiver-engine` (off `dev`); commits `adbb67e` (tick 1), `7422de7` (tick 2),
  + the audit/precision-fix commit. Not pushed (expedition PRs at close, signal-and-wait).
- **Controller mode:** dispatch-and-integrate (role-typed subagents; controller green-gates + is sole
  committer). Docs are the durable source of truth.
- **Landed + reviewed (bedrock):**
  - Thread 01 (recon) — closed.
  - Thread 02 (rung 1) — `DLNFibre.Core.Setup`: `Tuple`/`mult`/`Σ^r`/`Σ^{≤r}`/`fibre`. **closed, reviewed.**
  - Thread 03 (rungs 2–3) — `DLNFibre.Core.RankPattern`: Prop 3.1a inversion (`diff_cumul`/`cumul_diff`/
    `cumulDiffEquiv`). **closed, reviewed.**
  - Thread 04 (audit) — both SURVIVED on the math; two precision findings fixed (the `rankPatternEquiv`→
    `cumulDiffEquiv` rename; the stale phantom-`BoxSupported` docstring). **closed.**
- Whole lib green (1794 jobs), 0 sorries, axiom-clean. Cosmetic `abel_nf` info at RankPattern.lean:128.

## RESOLUTION (what is Proved, at exact scope)

- **Ambient objects** (Proved): `mult = A_N⋯A_1` over `CommRing k`, with the product-rank loci `Σ^r`/`Σ^{≤r}`
  and the fibre `mult⁻¹(B)` as `Set (Tuple d)` for a fixed `d : Fin (N+1) → ℕ`. Order pinned by witness.
- **Prop 3.1a** (Proved): the *abstract* cumul↔diff inclusion-exclusion inversion on half-plane-supported
  integer-indexed arrays over an `AddCommGroup`, as an `Equiv` (`cumulDiffEquiv`). The hypothesis
  `Supported` is shown necessary (off-stratum counter-witness), not vacuous.
- **Deferred / Cited (named, not hidden):** Prop 3.1b — that an *actual tuple's* rank pattern equals `cumul`
  of its Gabriel multiplicities — needs type-A Gabriel (rung 4). The matrix-side `submult`/`rankPattern`
  (thread 06). The `rlct = ½·codim` cap (Bundle 4, cited analytic bound) — out of this expedition.

## Next — rung 4 is the boundary (strategic call surfaced to operator)

Rung 4 (orbits ↔ Kostant via type-A Gabriel) is **build-from-scratch and not single-tide whole-in-reach**
(recon: "largest new infrastructure"). It is roadmapped, not nibbled. The strategic fork (full-build the
type-A Gabriel/interval-module decomposition — the reusable asset — vs cite Gabriel and prove the orbit↔
Kostant corollary on top) is surfaced to the operator. The `submult`/`rankPattern` follow-up (thread 06) is
a smaller, reachable item that unblocks Prop 3.1b and could precede rung 4.

## Drift guard

`Core` imports no `DLN`. Every result tagged Proved/Assumed/Cited/Deferred. No `Core` name asserts
Gabriel/tuple content (the `rankPatternEquiv` overclaim was caught + fixed). Prefer characterisations
(the `Equiv`) and the weakest hypotheses (shown necessary).
