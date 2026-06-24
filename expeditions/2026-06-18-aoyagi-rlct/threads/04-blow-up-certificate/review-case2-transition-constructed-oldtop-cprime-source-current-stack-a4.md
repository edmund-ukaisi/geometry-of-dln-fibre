# Review - Case 2 transition constructed old-top `Cprime` source-current stack

Date: 2026-06-24.

Reviewers: xhigh checker `Archimedes the 2nd`; Lean/API scout
`Ptolemy the 2nd`.

## Verdict

Accepted.  The reproduction is faithful to the current Lean interfaces and
keeps the result as finite transition/source-substitution/continuing-stack
bookkeeping.

## Boundary Check

- The wrapper should keep `hnext : J+2 <= prefixMinNat n (S+1)`.
- It should not add stopped-prefix, actual-width, or row-exhaustion
  hypotheses.
- The constructed obligation's terminal matrix remains the source-row
  reindexing of `[Cold; top(Cprime)]`; it is not `[Cold; Cprime]` and not
  original source rows.
- The successor following object is the formula-level
  `case2DisplayedSourceSuccessorFollowingFactor ... targetResidual C`, not a
  source-produced object.
- The suffix is the supplied family `Ctail`, consumed through
  `sourceSuffixProduct kappa Ctail S hSuffix`.

## Lean Shape

Place the wrapper in `SelectedEntryNormalCrossing.lean`, inside namespace
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate`, immediately
after the supplied-`Csucc` continuing source-current stack theorem.

Use the existing transition theorem's binders through the supplied boundary
`data`, then replace the generic `SourceProductionObligation` argument by
arbitrary `Cold`, `Cprime`, and `Ctail`.  Keep the constructed terminal matrix
proof-local; the statement should expose only

```text
C =
  case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime
    n data.stage_pos data.continuation targetResidual Cold Cprime
```

and the formula-level

```text
Csucc =
  case2DisplayedSourceSuccessorFollowingFactor
    n data.stage_pos data.continuation targetResidual C.
```

## Nonclaims

No source production of `Csucc` or `C'^(S+1)`, no suffix construction, no
successor chart construction, no transition regularity, no chart coverage, no
normal crossings, no pole order, no termination theorem, and no RLCT
consequence.
