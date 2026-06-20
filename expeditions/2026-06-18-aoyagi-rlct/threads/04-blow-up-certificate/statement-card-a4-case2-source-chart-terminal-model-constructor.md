# Statement card - A4 Case 2 source-chart terminal model constructor

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_terminalModelEntryIdeal_eq_relabelProductCandidate_of_sourceChartMap_actualWidth`

## Statement

Lean now combines the displayed source-chart Case 2 constructor with the
actual-width terminal relabel-model wrapper.  The theorem fixes the concrete
successor state

```text
pre.case2Succ(case2DisplayedSourceChartMap(...)(J+1,J+1))
```

and the corrected selected-label exponent update, then applies the stopped
terminal source-model entry-ideal theorem.

## Proved

- A constructor-level terminal source-model entry-ideal theorem for the
  concrete displayed source-chart boundary.
- The terminal model is indexed by the concrete relabelled post-state pivot
  weight.

## Assumed

- Actual next-width exhaustion.
- Pre exponent certificates, level invariant, and Case 2 least-value gap.
- A supplied Case 2 residual-block chart-family boundary.
- Supplied terminal old-top/suffix model fields.

## Not Proved

- No source-produced `C'^(S+1)`.
- No chart coverage or regularity from coordinates.
- No chart-produced terminal old-top/suffix data.
- No automatic Case 2 gap/tail transport after relabelling.
- No Jacobian arithmetic, normal crossings, RLCT extraction, termination,
  transition invariant, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-source-chart-terminal-model-constructor-a4.md`.
- Review artifact:
  `review-case2-source-chart-terminal-model-constructor-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- From `lean/`: `lake build DLNFibre`
- From `lean/`: `scripts/sorries`
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`
- `git diff --check`
