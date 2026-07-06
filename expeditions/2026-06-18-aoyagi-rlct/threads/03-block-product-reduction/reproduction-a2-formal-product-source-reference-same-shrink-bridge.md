# A2 p.13 Formal-product Source-reference Same-shrink Bridge

## Source Calculation

The p.13 formal-product chart measure can be compared to a concrete
source-image reference only after three facts are available on the same local
theta neighborhood `V`.

First, the formal-product measure is the raw-chart image of the raw source set,
restricted to the named p.13 source edge-family set:

```text
formalProduct =
  (map rawChart (rawHaar.restrict rawSourceSet)).restrict p13SourceSet.
```

Second, the theta-side raw map pushes the chosen theta reference on the same
`V` to that raw source restriction:

```text
map rawMap (thetaReference.restrict V) =
  rawHaar.restrict rawSourceSet.
```

Third, the raw chart composed with the raw map agrees as a pushed-forward
measure with the concrete source chart:

```text
map rawChart (map rawMap (thetaReference.restrict V)) =
  map sourceChart (thetaReference.restrict V).
```

Combining these equalities gives

```text
formalProduct =
  (map sourceChart (thetaReference.restrict V)).restrict p13SourceSet.
```

Therefore, for any chart piece contained in the p.13 source set,

```text
chartPiece subset p13SourceSet
```

restriction gives

```text
formalProduct.restrict chartPiece =
  (map sourceChart (thetaReference.restrict V)).restrict chartPiece.
```

Equivalently, this has the bounded-density socket form with constant density
`1`:

```text
formalProduct.restrict chartPiece =
  ((map sourceChart (thetaReference.restrict V)).withDensity (fun _ => 1)).restrict chartPiece,
```

and the density bound is pointwise `1 <= 1`.

## Lean Targets

The same-shrink equality is:

```text
formalProductMeasure_restrict_chartPiece_eq_sourceReference_restrict_of_formal_whole_eq_restrict_sourceSet_of_raw_push_of_twoStage
```

The bounded-density socket form is:

```text
formalProductMeasure_restrict_chartPiece_eq_withDensity_one_sourceReference_of_formal_whole_eq_restrict_sourceSet_of_raw_push_of_twoStage
```

Both are in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaFormalProductSourceReference.lean
```

## Boundary

This is measure bookkeeping on a fixed shrink.  It does not prove the raw
pushforward identity, the two-stage source-chart identity, determinant-chart
Haar transport, raw Haar normalization, original-prior transport, source-image
coverage, source-rank coverage, normal crossings, pole order, or RLCT
extraction.

## Kill Conditions

- Kill any use that treats this as proving the raw pushforward identity.
- Kill any use that silently combines equalities coming from different local
  neighborhoods `V`.
- Kill any use that reads the constant-density socket as a Haar or original
  prior transport theorem.
