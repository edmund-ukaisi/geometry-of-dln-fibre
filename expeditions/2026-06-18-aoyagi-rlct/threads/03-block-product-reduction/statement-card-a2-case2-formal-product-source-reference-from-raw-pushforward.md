# Statement Card - A2 Case 2 formal-product source-reference identity from raw pushforward

## Claim

On the local Case 2 passive-theta endpoint determinant/pivot sector, suppose
the passive-theta raw-order map sends the restricted theta reference measure to
the raw-order source-recursive restriction of a raw Haar measure:

```text
Measure.map rawMap (thetaReference.restrict V) =
  rawHaar.restrict rawSourceSet.
```

Then on any chart piece contained in the named p.13 source edge-family set, the
p.13 formal-product chart measure equals the chart-produced passive-theta
source reference after restriction.  Equivalently, on any measurable such chart
piece, it is a constant-density-`1` perturbation of that source reference, with
the tautological a.e. bound `1 <= 1`.

Public Lean names:

```text
exists_open_subset_formalProductMeasure_restrict_chartPiece_eq_sourceReference_restrict_of_case2PassiveTheta_rawMap_eq_restrict_rawSource

exists_open_subset_formalProductMeasure_restrict_chartPiece_eq_withDensity_one_sourceReference_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
```

## Inputs Used

- the Case 2 two-stage measure identity identifying the two-stage
  `rawMap`-then-`rawChart` pushforward with the direct endpoint `sourceChart`
  pushforward;
- the p.13 formal-product theorem identifying the formal-product raw-order
  chart measure with `Measure.map rawChart (rawHaar.restrict rawSourceSet)`,
  restricted to the p.13 source edge-family set;
- a measurable chart piece `chartPiece subset p13SourceSet`;
- the explicit raw-pushforward hypothesis above.

## Output

Lean should prove:

```text
formalProductMeasure.restrict chartPiece =
  (Measure.map sourceChart (thetaReference.restrict V)).restrict chartPiece
```

and the bounded-density wrapper:

```text
formalProductMeasure.restrict chartPiece =
  ((Measure.map sourceChart (thetaReference.restrict V)).withDensity
    (fun _ => 1)).restrict chartPiece
```

and

```text
∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict chartPiece,
  (fun _ => 1) E <= 1.
```

## Nonclaims

This does not prove the raw-pushforward hypothesis.  It does not prove full raw
Haar transport, original source-prior transport, source-image coverage,
source-rank coverage, source-image equality/coverage for arbitrary chart
pieces, scalar normalization, normal crossings, pole order, or RLCT extraction.
The density `1` is relative to the chart-produced source reference
`Measure.map sourceChart (thetaReference.restrict V)`, not a Haar
normalization statement.
