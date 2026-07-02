# Thread P2.e — two-worlds bridge view on the capstone predicate

**Seat:** lean-formaliser (`p2e-bridge`). **Branch:** `expedition/det-atlas-p2`.

## Target

The capstone predicate `Algebra.IsZariskiLocallyTrivialAffineProduct k Base M BaseLoc Fibre U`
(in `Core/RingTheory/Determinantal/LocalTriviality.lean`) names a ring/algebra object but sits at
the junction of two naming worlds — "base" is overloaded because `Spec` is contravariant. Build an
**additive** AG-facing view (no signature change) re-exposing the data under scheme names, so the
same object keeps correct names in both worlds.

## Delivered (additive — no change to the predicate)

In `Algebra.IsZariskiLocallyTrivialAffineProduct` namespace, a `FibrationView` section + four
accessors:

- `totalSpace (_A) : Type u := PrimeSpectrum Base` — the ambient total space (DLN: `Σ̄^r`).
- `fibreSpace (_A) : Type u := PrimeSpectrum Fibre` — the model fibre factor.
- `chartBaseSpace (_A) (_i : _A.ι) : Type u := PrimeSpectrum BaseLoc` — the per-chart fibration base.
- `chartProjection (A) (i : A.ι) : PrimeSpectrum (Localization.Away (A.chart i).chartElt) →
  PrimeSpectrum BaseLoc := PrimeSpectrum.comap (A.chart i).fibreModel.structMap.toRingHom` — the
  per-chart fibration projection comorphism `Spec(Away chartElt) → Spec BaseLoc`.

Plus the dictionary docstring (ring↔scheme table + `Spec`-contravariance note + the honest
per-chart-only boundary). DLN-side: a docstring note + a `rfl`-`example` in
`FibreZariskiLocalTriviality.lean`'s `Witness` section pinning `totalSpace = Spec(sweepSigmaRing) =
Σ̄^r`, `chartBaseSpace I = Spec(SchurLoc)`, `fibreSpace = Spec(sweepFibreRing)` on the DLN instance.

## Shape decision: accessors, not a `FibrationView` wrapper

Four bare `def`s in the predicate's namespace (dot-notation `A.totalSpace`, `A.chartProjection i`).
A wrapper `structure FibrationView` would add a second object carrying no new mathematical data —
construction burden, projection noise, ambiguity over extra invariants — for a pure renaming view.
Codex (xhigh, decorrelated) agreed: accessors are the cleaner Mathlib-grade shape; a wrapper only
pays off once a sizeable API with its own instances/coercions is built on the view.

## Honest boundary (name = content)

The scheme-side projection is **per-chart only** (domain `Spec(Away chartElt)`, the chart domain,
not all of `U`). A single global `π : U → base` is NOT built: it needs an actual gluing of the
per-chart projections from overlap-compatibility data (roadmap R1). The view asserts no global
projection — it exposes exactly the chartwise picture the predicate proves (chartwise triviality +
the 2-fold overlap cocycle).

## Codex consult refinements applied (all fidelity)

`codex/view-shape-prompt.md` + `codex/view-shape-answer.md`. Verdict: design basically right; four
doc fixes folded in:
1. `totalSpace` = ambient total space; local triviality holds over `U`, not all of it (don't
   overclaim "total space of the fibration").
2. `Spec Fibre` = **model** fibre; scheme-theoretic fibres over `Spec BaseLoc` points are base
   changes of it.
3. `Spec(Away chartElt)` **canonically corresponds to** `D(chartElt)`, not a definitional equality.
4. Global-`π` obstruction rephrased: "not constructed/proved from compatibility data here" rather
   than "needs the triple cocycle" (for maps into a fixed target, pairwise overlap-agreement is the
   gluing condition; a triple cocycle is the obstruction for gluing objects, not the right cite).

## Gates

- Full aggregator `scripts/lb DLNFibre` GREEN — 3834 jobs (no new file; additive to two existing).
- `scripts/sorries` = 0 sorry / 0 #exit / 0 native_decide / 0 axiom.
- `#print axioms` on all four accessors ⊆ `[propext, Classical.choice, Quot.sound]`.
- Aggregator `DLNFibre.lean` untouched (single-writer).
