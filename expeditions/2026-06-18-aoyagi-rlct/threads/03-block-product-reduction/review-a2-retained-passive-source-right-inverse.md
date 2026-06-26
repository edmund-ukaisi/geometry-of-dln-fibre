# Review - A2 retained-passive source right inverse

Date: 2026-06-26.

Reviewers: xhigh `Mencius the 3rd` and xhigh `Sagan the 3rd`.

## Scope

Audit the finite source right-inverse additions in:

```text
lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
reproduction-a2-retained-passive-source-right-inverse.md
statement-card-a2-retained-passive-source-right-inverse.md
```

## Verdict

Passed with API cleanup.

## Findings

The math/formalisation review found no correctness issue.  The checked points
were:

```text
step_lowerLeftBlock_L_of_L_eq_lowerUnitriangular
retainedPassiveSolvedA3_last_eq_of_productTailSum_eq
sourceReadbackSuffixState_lowerLeftBlock_L_eq_lowerLeftProductTailSum
sourceReadback_solvedA3_eq_lowerLeftBlock
edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart
```

The index shifts are consistent.  The lower-left tail recurrence uses
`p.succ` for the old suffix state and `p.castSucc` for the new one.  The final
`A3` sign matches the retained-passive solver:

```text
solvedA3 last = -(F3 - earlyTail) * CtopLast.
```

Since the full actual tail is `F3` and the final contribution is
`-(A3actual last * CtopLast^-1)`, the cancellation gives the actual final
lower-left block.

The Lean/API review requested two small public-surface improvements.  The
controller added an existential-hypothesis wrapper for the generic one-step
lower-left recurrence:

```text
step_lowerLeftBlock_L_of_exists_L_eq_lowerUnitriangular
```

and a pointwise-away-from-last wrapper for the final `A3` recovery:

```text
retainedPassiveSolvedA3_last_eq_of_productTailSum_eq_of_ne_last.
```

The broader suggestion to factor the two source-specific suffix inductions
into generic `ProductReduction` API remains a good cleanup target, but it was
not needed to bank this right-inverse checkpoint and would touch a wider API
surface.

## Nonclaims Check

The new theorem is a finite right inverse on `sourceRecursiveDetChart`.  The
review found no hidden assertion of openness, local homeomorphism,
source-rank coverage, equality with the whole source image, measure
pushforward, density/Jacobian transport, normal crossings, pole order, or RLCT
extraction.

## Verification

Controller verification after the API cleanup:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```

all passed.  The full build emitted only pre-existing linter warnings from
unrelated downstream/Core files.
