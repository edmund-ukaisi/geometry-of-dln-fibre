# Statement Card - A2 p.13 Formal-product Density Identity

## Claim

On any measurable chart piece contained in the named p.13 source edge-family
set, the restricted original edge-family volume is the formal-product p.13
chart measure with constant density equal to the inverse tuple-side Haar
scalar.

Public Lean name:

```text
originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_formalProductAbsDet_restrict_chartPiece
```

## Inputs Used

- additive Haar measure `m` on the raw topology-tuple space;
- measurable `chartPiece`;
- containment of `chartPiece` in the named p.13 source edge-family set;
- the already-proved p.13 formal-product/original-volume inverse-scalar
  comparison.

## Output

```text
originalEdgeFamilyVolume.restrict chartPiece =
  (formalProductMeasure.withDensity (fun _ => c^{-1})).restrict chartPiece
```

and the a.e. bound

```text
(fun _ => c^{-1}) <= c^{-1}
```

over `formalProductMeasure.restrict chartPiece`.

## Nonclaims

No passive-theta source-image equality, no original/source prior transport, no
source coverage, no scalar normalization, no normal crossings, no pole order,
and no RLCT extraction.
