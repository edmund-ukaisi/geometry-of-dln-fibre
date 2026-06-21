# Statement card - A4 Case 2 constructed source following factor

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.case2DisplayedConstructedSourceFollowingFactor`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceFollowingFactor_constructed`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPaperCprime_of_constructedSourceFollowingFactor`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_constructedSourceFollowingFactor_paperQP`

## Statement

Lean now constructs a total source-coordinate following factor from a supplied
pivot-first residual following matrix by zero-extending outside the old
residual-column block.  Restricting this total function back to the displayed
source following-factor domain recovers the supplied pivot-first matrix.

For the special supplied matrix `Q*Cprime`, Aoyagi's displayed inverse update
recovers the free chart-coordinate following factor:

```text
case2DisplayedPaperCprime(constructedSource(Q*Cprime)) = Cprime.
```

The supplied-boundary `Q/P` product identity is also repackaged with this
total source-coordinate following function.

## Proved

- A source-coordinate zero extension of any pivot-first following matrix.
- Exact recovery after applying `case2DisplayedSourceFollowingFactor`.
- The constructed-source form of `Q^-1*(Q*Cprime)=Cprime`.
- The supplied-boundary `Q/P` product identity with the old following factor
  represented by the total source-coordinate function.

## Assumed

- Displayed Case 2 continuation data.
- Supplied displayed-boundary data for the `Q/P` wrapper.
- The free chart-coordinate matrix `Cprime`.

## Cited

- None in Lean. This is finite reindexing and matrix algebra below the
  supplied-boundary interface.

## Deferred

- Full source production of the successor `C'^(S+1)`.
- Chart-produced recurrence or exponent post-data.
- Successor chart family, chart coverage, coordinate regularity, transition
  invariance, Jacobian arithmetic, normal crossings, RLCT extraction,
  arbitrary-pivot coverage, terminal relabeling, and printed-vector repair.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake env lean DLNFibre.lean`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
