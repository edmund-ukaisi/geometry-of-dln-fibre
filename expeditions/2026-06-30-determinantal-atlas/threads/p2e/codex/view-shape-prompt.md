# Codex consult — P2.e two-worlds bridge view shape (Lean 4 / Mathlib AG)

You are a decorrelated reviewer. I want a sharp verdict on the SHAPE and FIDELITY of a
small "bridge view" I just added to a Lean formalisation. Do not write Lean code; judge
the design.

## Context

We formalise the paper "Geometry of the fibers of the multiplication map of deep linear
neural networks". A capstone Lean predicate names a ring-theory object — a Zariski-locally
trivial affine product over an open of a prime spectrum:

```
structure Algebra.IsZariskiLocallyTrivialAffineProduct
    (k Base M BaseLoc Fibre : Type u) [comm-ring/algebra instances]
    (U : Set (PrimeSpectrum Base)) where
  ι : Type u
  chart : ι → AtlasFibreChart k Base M BaseLoc Fibre   -- per-chart data
  cover : (⋃ i, (PrimeSpectrum.basicOpen (chart i).chartElt : Set (PrimeSpectrum Base))) = U
```

Each chart carries (via `StandardFibreChart`):
- `chartElt : Base` cutting a principal open `D(chartElt) ⊆ Spec Base`;
- the chart's localized total ring `Total = Localization.Away chartElt`;
- `structMap : BaseLoc →ₐ[k] Total` (honest structure map presenting `Total` as a `BaseLoc`-algebra);
- an over-base trivialization `triv : Total ≃ₐ[BaseLoc] BaseLoc ⊗_k Fibre` + flatness.

## The naming tension (the whole point of the request)

The object lives at the junction of TWO naming worlds, and "base" is overloaded because
`Spec` is CONTRAVARIANT:

- **Ring/algebra world:** `Base` = base RING of the algebra; `BaseLoc` = the ring each
  chart is a product *over*. `structMap : BaseLoc →ₐ Total`.
- **Scheme/AG world:** `Spec Base` = TOTAL space (DLN: Σ̄^r), `Spec BaseLoc` = fibration
  BASE space (the rank-chart), `Spec Fibre` = fibre. `structMap`'s comorphism is the
  projection `π : Spec Total → Spec BaseLoc`.

The operator's request: DON'T pick one convention. Build an additive AG-facing VIEW so the
same object keeps its correct meaning + names in BOTH worlds. No signature change to the
predicate; keep `Base`/`BaseLoc`.

## What I added (additive accessors, in the predicate's namespace)

```
def totalSpace  (_A) : Type u := PrimeSpectrum Base
def fibreSpace  (_A) : Type u := PrimeSpectrum Fibre
def chartBaseSpace (_A) (_i : _A.ι) : Type u := PrimeSpectrum BaseLoc
def chartProjection (A) (i : A.ι) :
    PrimeSpectrum (Localization.Away (A.chart i).chartElt) → PrimeSpectrum BaseLoc :=
  PrimeSpectrum.comap (A.chart i).fibreModel.structMap.toRingHom
```

plus a dictionary docstring (ring-side ↔ scheme-side table + the one-line note that `Spec`
contravariance is what flips top↔bottom, so both names are correct in their own world).

## HONEST BOUNDARY I am asserting

The scheme-side projection is **per-chart only**. A SINGLE GLOBAL fibration morphism
`π : U → (base)` over all of `U` needs target-side global gluing (not built). The view must
NOT assert a global projection. It exposes the chartwise picture, matching what the
predicate proves (chartwise local triviality + 2-fold cocycle).

## Questions (give a direct verdict on each)

1. **Dictionary fidelity.** Is the ring↔scheme dictionary correct? In particular: is it
   right that `Spec Base` is the TOTAL space (not the base) and `Spec BaseLoc` is the
   fibration base, given `structMap : BaseLoc →ₐ Total` and that `comap structMap` goes
   `Spec Total → Spec BaseLoc`? Any term I've mislabeled?

2. **Per-chart scope honesty.** Is exposing the projection PER-CHART (domain
   `Spec(Away chartElt) = D(chartElt)`, the chart domain — NOT all of `U`) the honest
   scope, given the predicate only proves chartwise triviality + a 2-fold (pairwise)
   cocycle and NOT a triple cocycle / global gluing? Is there any sense in which I could
   honestly expose more (e.g. a global projection on `U`) without the gluing? I claim NO.

3. **API shape.** Accessors (4 bare `def`s in the predicate's namespace) vs a wrapper
   `structure FibrationView` bundling the same data. Which is the cleaner Mathlib-grade
   API for a pure VIEW that adds no new data and no new theorems — just renames existing
   fields under scheme names? I lean accessors (zero new data, no construction burden,
   `A.totalSpace` reads cleanly). Argue the other side if a wrapper is genuinely better.

4. **Any trap.** Is `chartProjection := PrimeSpectrum.comap structMap.toRingHom` the right
   morphism for "the local fibration projection"? Is the direction right (Spec is
   contravariant: ring map `BaseLoc → Total` gives space map `Spec Total → Spec BaseLoc`)?
   Anything about `totalSpace`/`fibreSpace` taking an unused `_A` argument that's ugly vs.
   just being plain `PrimeSpectrum Base`/`Fibre` abbreviations?

Be concise and decisive. Flag anything that is subtly wrong or overclaiming.
