# Review - A2 retained-passive source-recursive reconstruction spine

Date: 2026-06-26.

Reviewers: xhigh `Aquinas the 3rd` and xhigh `Jason the 3rd`.

## Scope

Audit the finite reconstruction-spine additions in:

```text
lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
reproduction-a2-retained-passive-source-recursive-reconstruction-spine.md
statement-card-a2-retained-passive-source-recursive-reconstruction-spine.md
```

## Verdict

Passed after API cleanup.

## Findings

The pen-and-paper/math review found no mathematical issue.  The
`p.castSucc`/`p.succ` suffix-state shifts are consistent with the backward
recursion.  The terminal `F2full_last = 0` case matches terminal `B = 0`.
The `A1` tail starts at index `succ 0`, so the dummy `A1seed 0` is not used.
The recovered active `solvedA1 0` correctly uses invertibility of the suffix
`Ctop` at index `succ 0`, obtained from `sourceRecursiveDetChart`.

The Lean/API review found one placement issue and one naming/generalisation
issue.  The generic Schur reassembly lemma was moved from
`RetainedPassiveCoordinates.lean` to `ProductReduction.lean`, next to the
generic block-corner and Schur residual API.  The endpoint-only `A1` tail
lemma was split into the reusable invariant

```text
sourceReadback_A1Tail_eq_sourceReadbackSuffixState_Ctop_of_ne_zero
```

and the endpoint corollary

```text
sourceReadback_A1TailAfterFirst_eq_sourceReadbackSuffixState_Ctop_succ_zero.
```

No hidden claim of image openness, local homeomorphism, source-rank coverage,
measure pushforward, density/Jacobian transport, normal crossings, pole order,
or RLCT extraction was found.

## Next Minimal Lemma

The next Lean target is the solved-`A3` analogue:

```text
sourceReadback_solvedA3_eq_lowerLeftBlock
```

stating that `(sourceReadback E).toCoordinateData.solvedA3 p` equals
`lowerLeftBlock (sourceReadbackTransformedEdge E p)` for every edge.  The
non-final cases should be seed projections.  The final case should use the
source-side `F3` lower-left suffix field and the retained-passive lower-left
tail sum.

After that, the final right-inverse theorem should reassemble each transformed
edge with `fromBlocks_schurReadbacks_eq` and cancel the upper-unitriangular
multiplier using `sourceReadback_F2full_eq_neg_sourceReadbackSuffixState_B`.

## Verification

The controller reran focused builds after the API cleanup:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

Both passed.
