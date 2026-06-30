# Brief — `foundation-lift` expedition (foundation-lift II)

## Central question

> **Lift the next batch of project-local-but-general modules in `DLNFibre.Core` to clean, Mathlib-grade
> reusable libraries — in three phases, each its own PR — continuing the "build the buildable" programme
> that #14's dimension stack opened.**

Built on **PR #14** (the affine dimension stack `DLNFibre.Core.Dimension.*`, merged on `origin/dev`
`00fb7238`). Same disposition (build-the-buildable; [`../../docs/policies/library-building.md`](../../docs/policies/library-building.md))
and the same proven machine as #14: generalise-and-re-home already-green code, per-rung re-gate, decorrelated
review on the crux rungs, lessons L1–L4 applied.

## Scope — three phases (recon-validated 2026-06-29; **branch from `origin/dev`**, local `dev` is stale)

| Phase | Library (eventual Mathlib home) | Content | Crux |
|-------|----------|---------|------|
| **P1 — Components & local dimension** | `Ideal.MinimalPrime` / `KrullDimension.Localization` | the **`TopDimMinPrimes*`** count engine (minimal primes → top-dim components → transport) + the localization no-drop dimension + the `minimalPrimes_sInf` SPIKE | P1-R5 per-prime no-drop |
| **P2 — Determinantal & elimination algebra** | `MvPolynomial.Ideal` / `LinearAlgebra.Matrix.Rank` | graph-ideal elimination (`ker aeval = graphIdeal`, height) + matrix rank ↔ vanishing minors | P2-R2 minor-rank `←` |
| **P3 — Smooth points & cotangent dimension** | `Smooth.Cotangent` / `AlgebraicGeometry.Tangent` | `CotangentJacobian` (cotangent dim = ker of the rectangular point-Jacobian, no smoothness) | P3-R1 cokernel-finrank |

**Recon corrections folded in** (the audit predated #14):
- **P1's general content is `TopDimMinPrimes{,Bridge,Radical,Poly,Localization}`**, NOT `SigmaComponents`/`ThetaComponentCount` (those stay DLN-local — `RepCoord`/`Tuple`/Kostant; only the one `minimalPrimes_sInf_of_finite_of_isPrime` SPIKE in `SigmaComponents` is general). The `TopDimMinPrimes{W0,W1W2,W2,ChartE,GfibAvoid}` are DLN keystones — stay local.
- **Already done — do NOT rebuild:** `SmoothPointRegular`+`SmoothLocalRelativeDimension` (→ #14 `Regular`/`Smooth`, `[IsAlgClosed]→[PerfectField]` done); `NoetherMonicPositioning` (→ #14 `Catenary`); `Matrix.rank_map_eq_of_injective` (already in `RankLocusClosed`); `minimalPrimes`/any-proper-ideal catenary (already in #14 `Codimension`). ⟹ **P3 is a single module.**
- The phases are **mutually independent** (each depends only on #14), so the branch-stacking is for clean git, not math.

## Execution (operator decision: autonomous, no pausing)

- **Drive P1 → P2 → P3 to completion without pausing for operator merges.** One **PR per phase**, opened as each phase lands, for **async** operator review/merge.
- **Stacked phase-branches** (`expedition/foundation-lift-p1` off `origin/dev`; `-p2` off `-p1`; `-p3` off `-p2`) so there are zero inter-phase conflicts; the operator merges in order whenever, and the controller retargets PR bases to `dev` as merges land.
- Per phase: **generalise-and-re-home** (the code is already green — lift to Mathlib-grade names/docstrings/minimal-hyps; mirror the eventual Mathlib namespace for extraction), per-rung re-gate, **decorrelated review on the flagged crux rung**.
- Cite only the monument: the SLT analytic core + Aoyagi `rlct = ½·codim` (unchanged, out of scope).

## The ladder

Full per-phase rung-ladder + the Mathlib-coverage findings in [`priorities.md`](priorities.md) (the recon report is the detailed brief).

## Closing criteria

- Three Mathlib-grade libraries lifted, each green / sorry-free / axiom-clean (`[propext, Classical.choice, Quot.sound]`), DLN consumers re-pointed to tag to them with **DLN payoff axioms unchanged**, each rung name=content + reviewed (fidelity + decorrelated Codex on the crux).
- Three per-phase PRs opened for async operator review/merge; the sibling-name-clash gate (`lean/CLAUDE.md`) cleared on each new top-level name.
- Exposition + synthesis at the close.

## Provenance

Coverage recon (scout, 2026-06-29) — the phased ladder + Mathlib coverage. Audit:
`/tmp/foundation-library-audit.md` (validated/corrected). Built on #14 (`origin/dev` `00fb7238`).
**Blind** to `origin/expedition/aoyagi-full` as before.
