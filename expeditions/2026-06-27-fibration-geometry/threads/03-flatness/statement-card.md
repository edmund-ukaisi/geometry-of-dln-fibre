# Statement card — S3 flatness (cheap-flatness verdict + side-facts; S3 target NOT met)

> **⚠ Scope (post-review, de-escalated).** The brief's S3 target — a single flat fibre-family
> projection `Flat π : mult⁻¹(rankROpen) → rankROpen` over the bundle base — is **NOT delivered**.
> What is delivered: the in-file **cheap-flatness verdict** + two genuinely-true flatness side-facts.
> A fidelity review (reviewer + decorrelated Codex) caught that the original "THE BUNDLE FLATNESS
> PAYOFF" framing overclaimed; the headlines and docstrings were de-escalated to name = content. The
> Lean is sound throughout (no math was changed); only the framing was corrected.

> **Cheap-flatness verdict (the S3 kill-condition, settled in-file, Codex-consulted).** The "structure
> map of the bundle's coordinate ring over the base" splits into TWO genuinely-different maps; flatness
> is cheap on both, but neither is the fibre-family flatness over the base, and **neither needed
> miracle/generic flatness**:
> 1. **chart inclusion** `Base → Total` — a localization, flat for free (`Localization.flat`),
>    independent of the Schur charts / rank bridge. The open-chart-inclusion fact, NOT the payoff.
> 2. **standard model over the auxiliary `SchurLoc`** `SchurLoc ⊗_k sweepFibreRing` — free (hence flat)
>    over `SchurLoc` by **generic base change** (true for any `k`-algebra; no DLN geometry). `SchurLoc`
>    is the in-chart Schur coordinate ring, NOT the bundle base. Also not the payoff.

> **⚠ Why the S3 target is not met (the blocker).** Routing fibre-family flatness through the atlas
> needs the chart trivialization to be **`SchurLoc`-linear** (`≃ₐ[SchurLoc]`). The atlas's
> `chartDsigAt_tensorEquiv` is only a **`k`-algebra** equiv (`≃ₐ[k]`), so the model's `SchurLoc`-
> flatness does **NOT** transport to the chart total ring `Localization.Away (chartDsigAt s t)`. The
> author's own target-setting Codex consult named exactly this missing rung
> (`codex/cheap-flatness-answer.md`). Building the `SchurLoc`-linear trivialization is the genuine
> open rung; until then S3's fibre-family flatness is OPEN.

## Lean deliverables (`DLNFibre.Core.FibreFlatness`, `lean/DLNFibre/Core/FibreFlatness.lean`)

- **`chartInclusion_flat`** — `(d) (r) (s) (t) : Module.Flat (sweepSigmaRing k d r)`
  `(Localization.Away (chartDsigAt d r s t))`. `[Field k]`. Proof `Localization.flat _ (powers …)`.
  The cheap chart-inclusion localization fact (the cheap-flatness verdict, chart-inclusion side).
  Honest, correctly scoped (NOT promoted to "bundle is flat").
- **`standardFibreModel_free`** — `Module.Free (SchurLoc …) (SchurLoc … ⊗[k] sweepFibreRing …)`.
  `inferInstance` (via `Module.Free.tensor`, canonical left-factor structure). Generic base change.
- **`standardFibreModel_flat`** — same shape, `Module.Flat`, `Module.Flat.of_free`. ⚠ Flatness over
  the **auxiliary** `SchurLoc`, NOT over the bundle base (generic base change; does not transport to
  the chart ring — the trivialization is only `k`-linear).
- **`flat_specMap_standardFibreModelOverSchur`** — `AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom`
  `(algebraMap SchurLoc (SchurLoc ⊗[k] sweepFibreRing))))`. Via `HasRingHomProperty.Spec_iff (P :=`
  `@Flat)` + `RingHom.flat_algebraMap_iff` + the model flatness. The model over the auxiliary
  `SchurLoc`, NOT the fibre family over the base.
- **`universallyOpen_specMap_standardFibreModelOverSchur`** — `AlgebraicGeometry.UniversallyOpen` of
  the same `Spec.map`. Via `UniversallyOpen.of_flat` (`[Flat]` from the previous;
  `[LocallyOfFinitePresentation]` genuinely discharged via `Algebra.FinitePresentation.quotient`
  (Noetherian) → `.baseChange` → `RingHom.finitePresentation_algebraMap` → `Spec_iff`).
- **`exists_chart_trivialization_onto_flat_model`** — `(d) (r) (hp) (hq) (s) (t) (σ) (τ) (hσ) (hτ)`
  `: Module.Flat SchurLoc (SchurLoc ⊗ sweepFibreRing) ∧ Nonempty (Localization.Away (chartDsigAt …)`
  `≃ₐ[k] SchurLoc ⊗ sweepFibreRing)`. `[Field k] [Infinite k]`. ⚠ A **conjunction of two separate
  facts** linked only by a `k`-linear equiv — does NOT establish flatness of the chart ring over a
  base (the equiv is not `SchurLoc`-linear). Records the atlas connection honestly, no synthetic
  structure asserted.

- **Gloss.** `Base = sweepSigmaRing k d r = O(Σ̄^r)`; `Total = Localization.Away (chartDsigAt s t)` a
  per-pivot chart ring; `SchurLoc = Localization.Away (detSchurS …)` the in-chart Schur direction;
  `sweepFibreRing = O(F)` the fibre coordinate ring. The atlas trivializes each `Total` as
  `SchurLoc ⊗_k sweepFibreRing` — only `k`-linearly.
- **Proved / Status.** All six headlines sorry-free, axiom-clean `[propext, Classical.choice,
  Quot.sound]`.
- **Assumed.** `[Field k]` throughout; `[Infinite k]` only for the atlas-connection witness. NO
  `[IsAlgClosed k]`, NO `[CharZero k]`.
- **Cited.** None new. All from Mathlib v4.29 + the in-repo atlas.

## Recorded gaps (honesty — name = content)

1. **PRIMARY: the S3 fibre-family flatness over the base is OPEN.** Blocker = the missing
   `SchurLoc`-linear trivialization `Total ≃ₐ[SchurLoc] SchurLoc ⊗_k sweepFibreRing`. With only the
   `k`-linear trivialization, `standardFibreModel_flat` is flatness over the *auxiliary* `SchurLoc`
   (generic base change), not over the bundle base.
2. **Global (single-morphism) flatness over all of `rankROpen`** would additionally need the
   target-overlap gluing (`targetOverlapTransition`, roadmap R1). Secondary to (1).
3. **`rankAtStalk` locally constant NOT included.** `Module.isLocallyConstant_rankAtStalk` needs
   `Module.FinitePresentation SchurLoc (SchurLoc ⊗ sweepFibreRing)` as a *module* (finite-rank vector
   bundle). The DLN fibre has positive dimension ⟹ not a finite module ⟹ corollary does not apply.
   `UniversallyOpen` (of the auxiliary-`SchurLoc` map) is the corollary that does apply.

## Review trail

- Fidelity review: PASS-WITH-NOTES → de-escalation actioned. The reviewer (+ decorrelated Codex)
  flagged `standardFibreModel_flat`'s "THE BUNDLE FLATNESS PAYOFF" docstring as an overclaim
  (generic base change over an auxiliary ring, severed from the chart ring by the `k`-only equiv) and
  flagged that the real S3 gap (missing `SchurLoc`-linear trivialization) was mis-located as only the
  global-gluing gap. Both corrected in this revision: headline framing de-escalated, theorems renamed
  (`…standardFibreModelOverSchur`), primary blocker recorded.

## Axiom check (`#print axioms`)

All six → `[propext, Classical.choice, Quot.sound]` (axiom-clean; no `sorryAx`).

## Build / gate

- `scripts/lb DLNFibre.Core.FibreFlatness` → green (3413 jobs), zero in-module warnings.
- `scripts/sorries` → `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `Core`-only: imports `FibreBundleLocallyTrivialFull`, `Mathlib.RingTheory.Flat.{Localization,Basic}`,
  `Mathlib.LinearAlgebra.TensorProduct.Basis`,
  `Mathlib.AlgebraicGeometry.Morphisms.{Flat, UniversallyOpen, FinitePresentation}`. Does NOT import
  `DLNFibre.DLN`.

## Controller wiring note

`lean/DLNFibre.lean` (single-writer aggregator) must add `import DLNFibre.Core.FibreFlatness` at the
end. I did NOT edit the aggregator.
