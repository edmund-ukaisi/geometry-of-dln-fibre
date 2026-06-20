# Statement card - A4 Case 2 identity-following actual-width boundary

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_actualWidth_terminalOriginalRowsIdentityFollowingBoundary`

## Statement

Lean exposes the displayed source-chart actual-width terminal boundary when
the supplied following matrix is the identity.  The theorem removes the
rightmost `* F` from the arbitrary-following boundary by specializing
`F = 1`.

## Proved

- Under actual-width exhaustion `n(S+1)=J+1`, the stopped terminal product uses
  original source rows `1..J+1`.
- The following matrix is specialized to the identity.
- The actual-width relabelled level invariant and exponent-domain certificate
  are packaged with the entry-ideal equality.

## Assumed

- The displayed Case 2 stage and continuation hypotheses.
- The pre-state exponent certificate, level invariant, and least-value gap.
- The residual-block chart-family regularity and transition interface.
- Finiteness of the following-column type `tau`, used to instantiate the
  arbitrary-following boundary.  Decidable equality is local to the proof.

## Cited

- None in Lean.  This is finite algebra and bookkeeping.

## Deferred

- Applying this to a source suffix requires the separate terminal-last suffix
  identity.
- Row-exhausted wide-next terminal wrappers.
- Chart coverage, source production of `C'^(S+1)`, chart-produced following
  products, Jacobian arithmetic, normal crossings/RLCT extraction,
  termination, transition invariance, and repair of the printed Case 2 vector
  mismatch.

## Review

- Review artifact:
  `review-case2-identity-following-actual-width-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
