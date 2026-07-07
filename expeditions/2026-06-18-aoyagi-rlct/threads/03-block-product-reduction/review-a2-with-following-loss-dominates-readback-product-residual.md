# Review - A2 with-following loss dominates readback product residual

Reviewer: xhigh read-only reviewer `Aquinas the 2nd`.

## Verdict

No findings.  The theorem statement, proof, reproduction, and statement card
match the intended local function comparison.

## Audit

The theorem

```text
exists_pos_const_eventually_readbackProductResidual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase_nhdsWithin_rankCut_of_sourceChart_image_eq
```

is a local eventual comparison on

```text
(p13SourceSet cap readback^{-1} V) cap sourceStratum.
```

It does not claim a measure comparison, source coverage, source-rank atlas
coverage, residual integrability, normal crossings, pole order, or RLCT.

The proof correctly:

- restricts the endpoint loss lower bound from `sourceStratum` to the rank-cut
  patch by subset/filter monotonicity;
- uses the image equality to write patch points as `sourceChart z`;
- uses determinant-sector membership for the fixed p.13 residual equality;
- uses the source-chart/readback left inverse for the readback residual
  equality;
- drops the regular coordinate square-sum by nonnegativity and nonnegative
  scalar multiplication.

The reproduction and statement card accurately record the assumptions,
conclusion, and deferred boundaries.

## Checks

The reviewer independently ran focused elaboration from the Lean package root:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaProductResidualBridge.lean
```

and confirmed the theorem axiom probe reports only:

```text
[propext, Classical.choice, Quot.sound]
```

## Status

Statement-card ready.
