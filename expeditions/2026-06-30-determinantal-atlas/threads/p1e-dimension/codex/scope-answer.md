**(A) BRICK-A VERDICT**

Fact from your report: Brick A is proved, zero-cited, and not an axiom/threaded citation. On that basis, yes: naming downstream results `_of_brickA` or “Cited” would be a precision violation by under-claiming. State the dimension theorem as proved, and name the proved load-bearing input in the docstring/proof comments.

I would only hunt harder if there is a second Brick A elsewhere. Cheapest grep:

```bash
rg -n "Brick A|Cited|cited|codimRepCanonical_productRankLocusLE_eq_cCodim|determinantal codim|height.*determinantal|Eagon|Northcott|Bruns|Vetter"
```

**(B) RE-HOME SCOPE**

Inference from your description: do not force the engine-bound headline into bare `Matrix`/`Ideal` if that requires dragging `RepCoord`, `canonicalCoord`, `codimRepCanonical`, `sigmaIdeal`, or `varietyDim` into a Mathlib-mirror module.

Right minimal `Dimension.lean` content:

- pure `Nat` arithmetic: `(n - r) * (m - r) + r * (n + m - r) = m * n`;
- closed-form rank-stratum parameter/dimension formula, if expressed only in matrix/chart terms already in `Basic/Strata/Schur`;
- possibly `cCodim ![n,m] r = (n-r)(m-r)` only if `cCodim` is already accepted as Core combinatorics and importing it does not pull the DLN orbit engine.

Engine-coupled `varietyDim_productRankLocusLE_stratum` should stay in its current Core/DLN-engine home, maybe cleaned to import the new arithmetic lemmas.

**(C) PRECISION NAMING**

Use names that say exactly which object is being measured.

I’d use:

```lean
Matrix.rankStratumDimFormula
Matrix.rankStratumCodimFormula
Matrix.rankStratumDim_add_rankStratumCodim
```

For concrete invariants, distinguish them explicitly:

```lean
Matrix.finrank_pivotRankChart_params_eq
Ideal.height_map_sigmaIdeal_away_eq_cCodim
varietyDim_productRankLocusLE_stratum
```

Avoid a name like `rankStratum_dimension_eq` unless the theorem really states a chosen dimension invariant, not just the polynomial `r * (n + m - r)`.

**(D) TRAPS**

Biggest trap: making `Dimension.lean` look Mathlib-mirror clean while it secretly imports the DLN orbit-codimension engine, or worse, restating proved Brick A as a cited assumption.

Cheapest guard: after edits, check imports and axioms separately:

```bash
rg -n "RepCoord|canonicalCoord|codimRepCanonical|sigmaIdeal|varietyDim|DLNFibre" Core/RingTheory/Determinantal/Dimension.lean
#check codimRepCanonical_productRankLocusLE_eq_cCodim
#print axioms codimRepCanonical_productRankLocusLE_eq_cCodim
```