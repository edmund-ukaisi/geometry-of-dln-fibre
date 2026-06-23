# Statement card - A4 Case 1/Case 2 selected-entry finite coverage

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`
- `case1CenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`

Private helper:

- `selectedEntryFamily_exists_chartPoint_chartMap_eq_value`

## Claim

The generic all-pivot finite selected-entry coverage theorem specializes to
Aoyagi's two finite all-pivot selected-entry centers already present in Lean:
the Case 2 residual-block center and the Case 1 center-generator set.  In each
case, every finite center value has a preimage in some chart of the finite
all-pivot selected-entry certificate.

## Inputs Kept Explicit

- for Case 2: `1 <= S` and `J + 1 <= prefixMinNat n (S + 1)`, used only to
  make the residual-block center nonempty;
- for Case 1: the existing nonempty old-generator token in
  `case1CenterGenerators n S J J1`;
- an ordered field coefficient type;
- an arbitrary finite center value function.

## Proved

For Case 2, Lean proves that for every

```text
value : {p // p in case2ResidualBlockPivotEntries n S J} -> K
```

there exists a chart index and chart point of
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate` whose chart
map is `value`.

For Case 1, Lean proves the analogous statement for every

```text
value : {g // g in case1CenterGenerators n S J J1} -> K.
```

Both proofs are definitional `simpa` specializations of the generic finite
selected-entry all-pivot coverage theorem.

## Not Proved

No analytic atlas coverage, no transition regularity, no arbitrary-pivot
Aoyagi source-coordinate formulas, no source production for successor matrices
or suffix products, no analytic Jacobian/volume-form control, no full
normal-crossing certificate, no pole order, and no RLCT extraction.

## Verification

Controller ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The focused build, full-library build, no-sorry/no-axiom scan, and diff
hygiene check passed through the shared-store `lb` workflow.  The full build
emitted only unrelated pre-existing Core warnings.

## Review

Xhigh review passed with no findings.  See
`review-case1-case2-selected-entry-finite-coverage-a4.md`.
