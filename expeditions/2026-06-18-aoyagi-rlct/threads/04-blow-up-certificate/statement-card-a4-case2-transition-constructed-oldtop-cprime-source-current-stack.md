# Statement card - A4 Case 2 transition constructed old-top `Cprime` source-current stack

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Name:

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_continuingSourceCurrentStack_constructedWithOldTopFromCprime_sourceSubstitution_of_displayed_normalized_ne_zero`

## Claim

On the displayed Case 2 normalized-coordinate overlap, the transition wrapper
for the continuing source-current stack now applies directly to the constructed
old-top/free-`Cprime` source following factor.

The theorem takes transition-generated displayed target data

```text
targetU = u * normalized(sourceChart,residual,(J+1,J+1))
targetResidual(q) = normalized(sourceChart,residual,q)
  / normalized(sourceChart,residual,(J+1,J+1))
```

and arbitrary old-top rows `Cold`, free displayed `Cprime`, and supplied suffix
matrices `Ctail`.  It constructs

```text
C =
  case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime
    ... targetResidual Cold Cprime
```

and uses the formula-level successor

```text
Csucc =
  case2DisplayedSourceSuccessorFollowingFactor ... targetResidual C.
```

The output keeps the existing transition chart-map equality and the displayed
source-substitution equality, then returns the continuing source-current stack
with the lower-left substitution block rewritten to the original source-selected
substitution block.

## Proved

- The constructed old-top/free-`Cprime` source following factor supplies the
  `SourceProductionObligation` needed by the existing transition stack wrapper.
- The proof-local terminal matrix for that obligation is the source-row
  reindexing of `[Cold; case2DisplayedFreeCprimeTop ... Cprime]`.
- The transition wrapper can consume that constructed obligation without
  adding stopped-prefix, actual-width, or row-exhaustion assumptions.

## Assumed

The theorem assumes the displayed normalized coordinate is nonzero, the target
data are exactly the transition-generated displayed data, the continuing guard
`J+2 <= prefixMinNat n (S+1)`, a displayed supplied chart-family boundary for
those target data, arbitrary `Cold` and `Cprime`, and a supplied raw source
suffix family `Ctail`.

## Cited

None in Lean.  The source motivation is Aoyagi PDF pp. 21-22, where the Case 2
continuing chart calculation transports the following block by
`C'_J^(S+1) = Q^-1 C_J^(S+1)`.

## Not Proved

No source production of `Csucc` or `C'^(S+1)`, no suffix construction, no
successor chart construction, no stopped terminal-prefix collapse, no
actual-width collapse, no transition regularity, no chart coverage, no analytic
Jacobian data, no normal crossings, no pole order, no termination theorem, no
RLCT consequence, and no repair of the printed Case 2 vector mismatch.

## Reproduction and Review

- Reproduction:
  `reproduction-case2-transition-constructed-oldtop-cprime-source-current-stack-a4.md`.
- Review:
  `review-case2-transition-constructed-oldtop-cprime-source-current-stack-a4.md`.

## Verification

- 2026-06-24, from `lean/`: `scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing` passed.
- 2026-06-24, from `lean/`: `scripts/lb DLNFibre` passed.
- 2026-06-24, from `lean/`: `scripts/sorries` reported
  `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- 2026-06-24, from expedition root: `git diff --check` passed.
