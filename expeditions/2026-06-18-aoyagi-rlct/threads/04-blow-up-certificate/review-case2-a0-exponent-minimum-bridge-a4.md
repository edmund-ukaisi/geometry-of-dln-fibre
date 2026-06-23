# Review - A4/A0 Case 2 exponent-minimum bridge

Date: 2026-06-23.

Status: xhigh source/math and Lean/API reviews passed.

## Reviewed Artifact

- `lean/DLNFibre/DLN/Aoyagi/Case2FiniteExponentBridge.lean`
- `reproduction-case2-a0-exponent-minimum-bridge-a4.md`
- `statement-card-a4-a0-case2-exponent-minimum-bridge.md`

Lean name reviewed:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge.exponentMinimum_eq_centerCard_div_two_of_forall_le
```

## Source/Math Review

Reviewer: `Euler the 2nd`.

Verdict: pass; no required fixes.

The reviewer confirmed that this is finite minimum bookkeeping matching
Aoyagi PDF p. 6's finite ratio-minimum formula and the Case 2 residual-block
bookkeeping on pp. 19-22.  The theorem uses only:

- an active coordinate and local ratio supplied by the previous bridge;
- an explicit global lower-bound hypothesis over all active coordinates.

It does not construct charts, prove the lower bound, prove order, or extract
an RLCT.

## Lean/API Review

Reviewer: `Schrodinger the 2nd`.

Verdict: pass; no required fixes.

The reviewer confirmed that the theorem has the right strength: it consumes
the bridge `B` and the explicit lower-bound hypothesis

```text
forall p' in D.activePairs, centerCard/2 <= D.ratioAt p'
```

and delegates exactly to
`AoyagiNormalCrossingExponentData.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le`.

## Verification

Focused checks passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Case2FiniteExponentBridge.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Case2FiniteExponentBridge
cd lean && lake env lean DLNFibre.lean
```

The Lean/API reviewer also ran the sorry scanner on the module and found no
forbidden constructs.

## Boundary

This review does not certify construction of the A0 exponent data `D`, a
coordinate-production theorem for `p`, proof of the global lower bound, an
exponent-order theorem, chart production, analytic normal-crossing chart data,
analytic Jacobian/volume-form control, pole order, or RLCT extraction.
