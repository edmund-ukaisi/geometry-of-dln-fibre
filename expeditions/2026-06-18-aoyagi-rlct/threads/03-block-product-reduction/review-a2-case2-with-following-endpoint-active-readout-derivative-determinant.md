# Review - A2 Case 2 with-following endpoint active-readout derivative determinant

Date: 2026-07-02.

Reviewer: xhigh read-only audit `Erdos the 2nd`.

## Verdict

Pass.  The target is the correct next A2 formalisation step when stated as the
determinant of the source-type endomorphism

```text
endpointTopologyTupleActiveReadout n e o
case2PassiveThetaWithFollowingFactorEndpointTopologyTuple.
```

It is not a determinant theorem for the bare endpoint topology-tuple map `Y`.

## Scope Check

The reviewer confirmed:

- no determinant-sector hypothesis is needed;
- no selected-pivot-nonzero hypothesis is needed for the determinant equality
  itself, although pivot nonzero remains needed downstream for inverse
  readback, injectivity, local COV, and positive lower bounds;
- `hcont` is redundant mathematically from `hnext`, but acceptable because the
  endpoint constructors require it;
- the `Fintype` hypotheses are legitimate for finite determinant/product
  coordinate determinant instances;
- the proof correctly reduces through the pointwise endpoint active-readout
  equality rather than pretending to compute a determinant for arbitrary
  endpoint reindexing.

## Density Check

The selected-entry source density is the expected Case 2 factor:

```text
sourceDensity pivot y = |y pivot| ^ (center.erase pivot).card.
```

For the current theorem, `center` is the Lean successor residual center
`case2ResidualBlockPivotEntries n S (J + 1)`, so the paper's informal
`|u|^(mn - 1)` should be read as the selected residual block cardinality minus
one.  It is not the full active `C` inventory and not the added following
factor.

Passive fields and the following factor contribute determinant `1` in this
normalized source-type statement.  The following factor here is Lean's
normalized retained/raw `C(0)` coordinate, not Aoyagi's original untransformed
following matrix.

## Required Nonclaims

The docs and docstrings satisfy the needed boundary:

- not a theorem about the bare endpoint topology tuple map `Y`;
- not a local change-of-variables theorem;
- not determinant-chart Haar/reference-image equality;
- not raw-order Haar or source-prior transport;
- no `retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)` factor
  belongs here; that factor appears only for `topologyTupleEdgeRawOrder o Y`;
- no normal crossings, pole order, or RLCT.

## Residual Risk

When a later theorem is stated for the raw map

```text
topologyTupleEdgeRawOrder o Y,
```

it must multiply by the retained-passive raw-order determinant factor and must
not double count the selected-entry monomial blow-up factor.
