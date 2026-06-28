# Statement card - A4 Case 2 concrete selected-entry source production

Status: Lean implementation landed and reviewed.

Reproduction:
`reproduction-selected-entry-analytic-atlas-case2-concrete-source-production-a4.md`.

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAnalyticAtlasCase2FinalBridge.lean`

Name:

- `SelectedEntryCase2DisplayedA0SourceProduction.of_case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate`

## Claim

For the concrete finite all-pivot Case 2 selected-entry chart certificate

```text
Cnc =
  case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate n hS hcont,
```

the displayed continuing Case 2 source calculation constructs the
nonvacuous source-production payload

```text
SelectedEntryCase2DisplayedA0SourceProduction Cnc.
```

The payload contains:

- the displayed continuing Case 2 center-square/formal-Jacobian certificate
  built by
  `sourceChartMap_continuingCenterSqFormalJacobianCertificate_withoutChartFamily`;
- an arbitrary all-pivot chart coordinate `(c, 0)`;
- the A0 exponent-coordinate bridge obtained from
  `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.localExponentCoordinateBridge_anyChart`.

## Inputs Kept Explicit

- `1 <= S`, `S <= Lcase`;
- the continuation guard `J+1 <= prefixMinNat n (S+1)`;
- the continuing guard `J+2 <= prefixMinNat n (S+1)`;
- the old exponent certificates;
- the level invariant and least-value-gap data;
- the displayed chart variables `u`, `residual`, and following factor `Ccase`;
- the concrete all-pivot chart index `c`.

## Proved

The concrete all-pivot finite chart certificate no longer needs an opaque
`SelectedEntryCase2DisplayedA0SourceProduction` assumption.  Its
source-production field can be inhabited from the displayed Case 2 finite
certificate and the existing local exponent-coordinate adapter.

## Not Proved

No arbitrary `Cnc` source-production theorem, no analytic atlas construction,
no coverage, no chart or transition regularity, no unit regularity, no analytic
Jacobian/volume-form compatibility, no branch termination, no global
active-ratio lower bound, no chart-count bound, no normal crossings, no pole
order, and no RLCT extraction.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb \
  DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasCase2FinalBridge
```

The build completed successfully with the local shared Lake directory.

## Review

Xhigh review passed after correcting the reproduction note's description of
the A0 wrapper.  See
`review-selected-entry-analytic-atlas-case2-concrete-source-production-a4.md`.
