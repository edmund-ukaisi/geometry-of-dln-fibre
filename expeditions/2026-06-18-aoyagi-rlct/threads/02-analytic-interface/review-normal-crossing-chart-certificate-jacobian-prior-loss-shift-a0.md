# Review - Chart-certificate Jacobian-prior loss shift

Date: 2026-06-23.

Reviewers: xhigh Lean/API scout `Beauvoir`, xhigh hardener `Volta`, and
source-direction scout `Ptolemy`.

## Verdict

Accepted as a small A0 checkpoint, with scope restricted to certificate
algebra on supplied chart data.

## Lean/API Check

`Beauvoir` checked the Lean shape in
`lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean` and found the operation
straightforward:

```text
AoyagiNormalCrossingChartCertificate.jacobianPriorLossShift
jacobianPriorLossShift_lossExp
jacobianPriorLossShift_jacobianPriorExp
exponentData_jacobianPriorLossShift
exponentData_exponentMinimum_jacobianPriorLossShift
exponentData_exponentOrder_jacobianPriorLossShift
```

The proof combines the old Jacobian/prior monomial identity with the extra
coordinate monomial using associativity, `Finset.prod_mul_distrib`, and
`pow_add`.  The finite minimum/order consequences are projections to the
already proved exponent-data shift.

Focused build passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.NormalCrossingInterface
```

## Hardener Check

`Volta` found no blocking overclaim, provided the statement card uses the
certificate-algebra wording.  The operation modifies a supplied
`jacobianPrior` field by multiplying a coordinate monomial and records the
corresponding exponent update.  It is not a theorem that Aoyagi's regular
variables have been analytically constructed or that a volume form has been
computed.

Required nonclaims:

- no chart construction or coverage;
- no transition regularity;
- no analytic nonvanishing neighbourhood;
- no analytic Jacobian/volume-form theorem;
- no regular-suspension theorem;
- no pole order or RLCT extraction;
- no use of extraction on a reduced certificate followed by adding `m/2`.

## Source-Direction Note

`Ptolemy` recommended that the next source-moving A4/A0 slice should return to
the selected-entry microcertificate side, possibly by packaging existing
`sourceChartPoint` identities.  That is compatible with accepting this A0
checkpoint: this shift is reusable certificate plumbing, while selected-entry
source packages remain the better next source-production direction.

## Controller Decision

Keep the chart-certificate shift because it is non-vacuous certificate algebra
and projects definitionally to the already reviewed finite exponent-array
shift.  Do not promote it to regular-coordinate additivity or to an analytic
extraction-transfer theorem.
