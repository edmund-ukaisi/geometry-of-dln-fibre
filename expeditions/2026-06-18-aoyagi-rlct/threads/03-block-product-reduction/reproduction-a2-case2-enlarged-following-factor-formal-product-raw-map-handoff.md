# Reproduction - A2 Case 2 enlarged following-factor formal-product raw-map handoff

Date: 2026-07-02.

Status: source-chart measure handoff after the enlarged following-factor
raw-order bridge.  This note does not prove the raw-map Jacobian or density.

## Source Boundary

Aoyagi Lemma 2 and Theorem 3, PDF pp. 10-13, give the retained-passive
Schur/product coordinate algebra.  They do not state a measure pushforward
identity from the enlarged Case 2 source coordinates to raw p.13 topology
tuple coordinates.  The Case 2 pages, PDF pp. 19-22, give the local
selected-pivot and following-factor normalization context, but not the
formal-product/source-image density theorem.

The previous frontier note

```text
reproduction-a2-case2-enlarged-following-factor-raw-density-frontier.md
```

records the actual remaining density calculation.  The formal variables
`yNext` and `F` are normalized retained-coordinate choices: `yNext` supplies
the local fixed-pivot selected-entry chart for raw `C(1)`, and `F` is the
normalized retained/raw `C(0)` block after the following-factor transform and
endpoint/reindexing conventions.  They are not verbatim global formulas from
the PDF and do not cover the whole Case 2 source image without a finite pivot
cover.

## Lean Inputs Already Proved

The enlarged raw-order bridge proves that on a local open set `V`

```text
rawChart (rawMap z) = sourceChart z
```

and that the one-stage and two-stage raw-order pushforwards agree with the
direct source-chart pushforward:

```text
Measure.map (fun z => rawChart (rawMap z)) (thetaReference.restrict V)
  = Measure.map sourceChart (thetaReference.restrict V)

Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V))
  = Measure.map sourceChart (thetaReference.restrict V).
```

The retained-passive raw-order Jacobian theorem already identifies the p.13
formal-product chart measure as

```text
Measure.map rawChart (rawHaar.restrict rawSourceSet)
```

restricted to the fixed-base p.13 source edge-family set, after the existing
formal raw-order determinant density has been absorbed into the raw-order
source-recursive chart.

## Handoff Calculation

Assume the missing raw-map pushforward identity explicitly:

```text
Measure.map rawMap (thetaReference.restrict V)
  = rawHaar.restrict rawSourceSet.
```

Then, for any chart piece contained in the p.13 source edge-family set,

```text
formalProductMeasure.restrict chartPiece
  = (Measure.map sourceChart (thetaReference.restrict V)).restrict chartPiece.
```

This is only associativity and restriction bookkeeping:

1. The formal-product measure is
   `Measure.map rawChart (rawHaar.restrict rawSourceSet)` restricted to the
   p.13 source edge-family set.
2. The raw-map hypothesis replaces `rawHaar.restrict rawSourceSet` by
   `Measure.map rawMap (thetaReference.restrict V)`.
3. The enlarged raw-order bridge replaces the two-stage map by the direct
   source-chart map.
4. Restricting to a smaller `chartPiece` inside the p.13 source edge-family
   set removes the outer p.13-source restriction.

In the bounded-density contract shape this is the special case with
constant density `1` relative to the chart-produced source reference
`Measure.map sourceChart (thetaReference.restrict V)`.

## Kill Conditions

- Do not read the raw-map pushforward identity as proved.  It is the remaining
  finite-dimensional change-of-variables/Jacobian problem.
- Do not use this handoff as evidence for raw-Haar transport, source-prior
  transport, a bounded-density theorem for the actual unweighted source
  coordinates, source-image coverage, normal crossings, pole order, or RLCT.
- Do not forget that the fixed selected-entry chart is local to a nonzero
  pivot sector.
- Do not identify `F` with Aoyagi's original untransformed following matrix;
  it is the normalized retained/raw `C(0)` coordinate.

## Next After This Handoff

The next real density task remains to prove, on a small source box, the
raw-map change-of-variables statement with the correct density convention.
That calculation must combine:

```text
retained-passive raw-order determinant factor
selected-entry source density for C(1)
identity following-factor coordinate for C(0)
endpoint/reindexing constants
```

and then state whether the density is source-side, raw-target-side, or
source-image-side after readback.
