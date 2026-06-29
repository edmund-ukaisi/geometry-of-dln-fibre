# Priorities — `dimension-stack` (taste ledger)

Controller proposes by VOI; **operator edits this file directly**. Foundation-first, build-the-buildable
([`../../docs/policies/library-building.md`](../../docs/policies/library-building.md)).

## The recon (opening wave) — CLOSED 2026-06-28

The AG-foundations scout produced the library ladder. **Headline = the affine dimension stack (entry 1)** —
field-general, `Tuple`-free, Mathlib-absent (grep-verified), and among the most-requested missing Mathlib
commutative-algebra facts (upstream-worthy). **Entry 2 (smooth ⟹ regular)** sits directly on it. Entries 3–5
(orbit-geometry capstone, type-A Gabriel/`Ext`, q-series) stay **DLN-local** — fused to `Tuple`/box-moves;
calling them "general" today would overclaim. Build-vs-cite line: entries 1–2 buildable detail; the analytic
`rlct = ½·codim` is the monument (Cited).

## The ladder (rungs)

| rung | item | source module(s) | target namespace | status |
|------|------|------------------|------------------|--------|
| **R0** | **gate** — throwaway generalisation pass on `NullstellensatzCodim` (strip `RepCoord d`, `σ : Type*`, general `k`, comment out the `[IsAlgClosed]` geometric reading) → confirm the field-general core's *exact* minimal hyps; **revert** (finding is the deliverable). + Mathlib master/PR in-flight check for `IsCatenary` / the catenary equality. | `NullstellensatzCodim` | — | **in flight** |
| R1 | integral-extension dimension invariance (`ringKrullDim_eq_of_integral_injective` + going-up chain-lift) | `IntegralDimension` | `Core.Dimension.Integral` (↔ `Mathlib.RingTheory.KrullDimension.Integral`) | pending |
| R2 | polynomial-ring catenary (L5) + monic positioning — handle the `private` Mathlib Noether-normalization substitution **in-repo** (re-derive / use the public `exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit`); do **not** block on an upstream de-privatise PR | `NoetherMonicPositioning`, `PolynomialDimension` | `Core.Dimension.Catenary` | pending |
| R3 | finite-type-domain catenary (L4d) + closed-point corollaries (`height_eq_ringKrullDim_of_isMaximal`, local↔global) | `AffineDomainDimension` | `Core.Dimension.Catenary` | pending |
| R4 | codim bridge (L0): `varietyDim`, `height(vanishingIdeal Z) + varietyDim Z = card` — **split** the field-general catenary/codim core from the `[IsAlgClosed]` geometric `varietyDim` reading | `NullstellensatzCodim` | `Core.Dimension.Codimension` | pending |
| E1 | étale local-dimension bridge + `Ideal.height_eq_under_of_etale` | `FlatQuasiFiniteHeight`, `SmoothLocalRelativeDimension` | `Core.Dimension.Smooth` | pending |
| E2 | smooth point ⟹ regular local ring, with the **`[IsAlgClosed] → [PerfectField]`** generalisation | `SmoothPointRegular` | `Core.Dimension.Smooth` | pending |
| RF | retrofit DLN consumers (`codimRep`/`codimRepCanonical`/orbit-dim/fibre-codim) to tag to the general core; delete bespoke; green-gate | (consumers) | — | pending |

## Highest-suspicion (decorrelated-review the crux)

R2 monic-positioning (the `private`-Mathlib interaction); R4 the field-general / `[IsAlgClosed]` split-point;
E2 the `[IsAlgClosed] → [PerfectField]` weakening (confirm no later lemma silently re-needs algebraic
closure — the scout flagged both R4 and E2 as asserted-from-docstring, not trial-built).

## Roadmap (future expeditions — NOT this one)

orbit-geometry capstone de-`Tuple`-coupling (recon entry 3); type-A Gabriel/`Ext` (4); q-series (5); the
actual mathlib4 upstream PR process; package extraction to a shared library (surface as a **knowing
decision** when a cross-repo dependency is wired).
