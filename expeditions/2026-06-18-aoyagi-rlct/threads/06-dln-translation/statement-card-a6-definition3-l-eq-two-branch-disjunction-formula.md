# Statement card - A6 Definition 3 `L=2` branch-disjunction formula

Date: 2026-06-26.

## Lean declarations

File:
`lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`

New branch package propositions:

```text
AoyagiDefinition3SourceData.L2RepeatedPositiveTheorem2FormulaBranch
AoyagiDefinition3SourceData.L2TriangleOddTheorem2FormulaBranch
AoyagiDefinition3SourceData.L2TriangleEvenTheorem2FormulaBranch
```

New theorem:

```text
AoyagiDefinition3SourceData.exists_L_eq_two_theorem2Formula_branchDisjunction_of_sourceData
```

## Statement

For `L=2`, suppose the source-range reduced widths are natural values
`w1,w2,w3` and suppose some Definition 3 source data exists:

```text
exists ell C, AoyagiDefinition3SourceData 2 ell H r C.
```

Lean proves that at least one explicit finite Theorem 2 branch package exists:

```text
repeated-positive ell=1 package
or
triangle odd ell=2 package
or
triangle even ell=2 package.
```

The repeated branch carries positivity and a repeated-equality disjunction.
The triangle branches carry all three triangle inequalities and the parity tag
of `w1+w2+w3`.

## Source reproduction

`threads/06-dln-translation/reproduction-definition3-l-eq-two-branch-disjunction-formula-a6.md`

This composes the already reviewed source-data classification
`exists_sourceData_iff_repeatedPositive_or_triangle_of_L_eq_two` with the
already reviewed no-`hr` formula wrappers.  It uses Aoyagi PDF pp. 8-9 and the
branch-selection audit
`threads/06-dln-translation/source-audit-definition3-branch-selection-a6.md`.

## Review

`threads/06-dln-translation/review-definition3-l-eq-two-branch-disjunction-formula-a6.md`

## Verification

Whitespace and forbidden-marker checks passed:

```text
git diff --check
cd lean
scripts/sorries
```

Focused module build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.Definition3Bridge
```

## Nonclaims

This is finite branch dispatch only.  It does not choose a canonical branch,
prove branch independence, identify a unique lambda/order from arbitrary
source data, add a final socket, construct Eq5 payloads or charts, prove
normal crossings, identify pole order, or extract RLCT.
