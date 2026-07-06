# Reproduction - A2 Case 2 formal-product/source-image coordinate-count gate

Date: 2026-07-06.

Status: pen-and-paper coordinate gate completed and independently checked by
xhigh read-only scout `Nash`. This is a gate for a future local
change-of-variables theorem; it is not a Lean theorem and it proves no measure
transport.

## Source Boundary

Aoyagi Lemma 2, PDF pp. 10-11, gives the one-step Schur substitution

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = -A3 A1^{-1} A2 + A4,
```

with the inverse formulas

```text
A2 = -A1 F2,
A3 = -F3 A1,
A4 = C4 + A3 A1^{-1} A2.
```

Aoyagi Theorem 3, PDF pp. 11-13, iterates this coordinate change through the
product and displays the final reduced block

```text
[ C1 - Er,  -F2
  -F3,       prod_s C^(s) - F3 F2 ].
```

These pages justify the block-coordinate algebra and the presence of the
active `C` factors. They do not state a measure pushforward theorem comparing
the p.13 formal-product chart measure with the image of a theta-domain
reference measure.

## Lean Coordinate Models

Let the three post-pivot endpoints be

```text
k0 = tau,
k1 = Case2ResidualColIndex n S (J + 1),
k2 = Case2ResidualRowIndex n S (J + 1).
```

The full retained-passive p.13 product tuple is

```text
TopologyTuple =
  A1passive,
  F2,
  A3passive,
  C,
  Ctop,
  F3,
```

where, in Case 2, the active `C` field has two matrices:

```text
C 0 : Matrix k1 k0 R,
C 1 : Matrix k2 k1 R.
```

This is the coordinate tuple used by the p.13 formal-product measure `muP13`
in the downstream original-volume/readback finite-integral bridge.

The plain source domain

```text
Case2PassiveTheta
```

stores the common passive fields

```text
A1passive, F2, A3passive, Ctop, F3
```

and selected-entry center coordinates

```text
yNext : Center n S J -> R.
```

Those selected-entry coordinates chart the successor residual block, hence
they supply the active `C 1` block after the selected-pivot chart. They do not
supply a free active `C 0` block.

The enlarged source domain

```text
Case2PassiveThetaWithFollowingFactor
```

adds

```text
followingFactor : Matrix k1 tau R.
```

Under the endpoint identification

```text
eNext : tau ~= k1,
```

this is exactly the missing active `C 0 : Matrix k1 k0 R` field.

## Field-By-Field Count

Write `P` for the number of scalar coordinates in the common passive fields

```text
A1passive, F2, A3passive, Ctop, F3.
```

Then the plain passive-theta source has

```text
dim Case2PassiveTheta = P + dim(C 1).
```

The full p.13 formal-product tuple has

```text
dim TopologyTuple = P + dim(C 0) + dim(C 1).
```

Therefore plain `Case2PassiveTheta` is lower-dimensional by

```text
dim(C 0) = card(k1) * card(k0).
```

With the Case 2 endpoint equivalence `tau ~= k1`, this missing dimension is
`card(k1)^2`. A measure supported on the plain source image cannot dominate
ambient p.13 formal-product measure on a full-dimensional chart piece unless
one has restricted the target to that lower-dimensional produced image and
changed the target measure accordingly.

For the enlarged source,

```text
dim Case2PassiveThetaWithFollowingFactor
  = P + dim(C 1) + dim(followingFactor)
  = P + dim(C 1) + dim(C 0)
  = dim TopologyTuple.
```

Thus `Case2PassiveThetaWithFollowingFactor` passes the coordinate-count gate
for a local p.13 formal-product/source-image change of variables.

## Consequence For The Frontier

The old target

```text
muP13.restrict chartPiece
  <= D * Measure.map plainSourceChart (thetaReference.restrict V)
```

is not a viable ambient p.13 theorem for plain `Case2PassiveTheta`. It can
only be used for chart pieces already lying in the produced lower-dimensional
image together with a target measure that is the corresponding image measure,
not the ambient full p.13 formal-product measure.

The viable full-dimensional target is the with-following chart:

```text
muP13.restrict chartPiece
  <= D * Measure.map withFollowingSourceChart
        (withFollowingReference.restrict V),
```

or preferably an equality with an explicit Jacobian density, with
`chartPiece` contained in the produced same-shrink source image.

## Remaining Obligations

The coordinate count removes one ambiguity but does not prove the local
change-of-variables theorem. The remaining obligations are:

1. Prove the exact same-shrink image set used by the theorem, for example
   `sourceChart '' V = p13SourceSet cap readback^{-1} V` or the smaller
   produced-image version actually consumed downstream.
2. Prove endpoint image equality for the with-following endpoint topology
   tuple on the local patch.
3. Compute the explicit source-to-p13 Jacobian density, or compose already
   formalized determinant-density pieces without replacing them by arbitrary
   Radon-Nikodym densities.
4. Prove local positivity and boundedness of the density after shrinking.
5. Keep determinant/raw Haar transport and original-prior transport separate
   unless their own source-to-measure comparison theorem is proved.

## Independent Check

Xhigh read-only scout `Nash` checked the Lean field lists against the p.13
formal-product tuple and agreed on the gate result: plain
`Case2PassiveTheta` is missing the active `C 0` matrix, while
`Case2PassiveThetaWithFollowingFactor` adds exactly that missing block and is
dimension-correct for the full p.13 chart-piece coordinate model.

The controller correction to the scout wording is that the safest count is
field-by-field: the common passive block `A3passive` should not be inferred
from prose alone. The conclusion is unchanged because the only non-common
field is `C 0`.

## Nonclaims

No formal-product/source-image domination, source-image coverage beyond the
chosen image hypothesis, endpoint determinant/raw Haar transport, raw-map
pushforward, source-to-raw Jacobian theorem, original-prior transport,
normal-crossing theorem, pole-order theorem, or RLCT extraction is proved
here.
