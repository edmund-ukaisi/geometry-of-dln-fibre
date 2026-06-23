# Review - selected-entry finite normal-crossing microcertificate

Date: 2026-06-23.

Reviewer: xhigh fidelity/bedrock reviewer `Confucius the 2nd`.

Status: passed after polish.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-selected-entry-normal-crossing-microcertificate-a4.md`;
- `statement-card-a4-selected-entry-normal-crossing-microcertificate.md`.

The review checked whether the certificate is genuinely local to the finite
center, whether the non-pivot residual coordinates match the formal determinant
exponent, and whether the Case 2 bridge overclaims global A0 chart data or
RLCT content.

## Findings

No substantive formalisation or mathematical issue remains.

The Lean certificate is local.  Its parameter type is `center -> K`, its loss
is only the square-sum over `Finset.univ : Finset center`, and the chart map
only fills finite center coordinates.  It does not encode a total DLN loss,
chart coverage, source production, analytic regularity, or RLCT extraction.

The residual-coordinate indexing matches the formal determinant exponent.  The
chart residual variables are indexed by `center.erase pivot`, and the formal
Jacobian/prior exponent is exactly `(center.erase pivot).card`.

The Case 2 specialization uses `case2ResidualBlockPivotEntries n S J` with
the displayed pivot-membership hypothesis.  The local bridge constructs the
existing Case 2/A0 exponent-coordinate bridge only for this microcertificate's
own exponent data; the Lean docstring and expedition notes explicitly deny a
global A0 chart-family, global active-ratio, pole-order, or RLCT claim.

## Incorporated Polish

- The statement card now lists all public theorem names in the new module.
- The reproduction source anchor now separates Aoyagi PDF p. 5 for the
  square-sum convention from Aoyagi PDF p. 6 for the normal-crossing exponent
  display.

## Residual Risk

The existing bridge type name `Case2DisplayedContinuingA0ExponentCoordinateBridge`
remains stronger than its fields: it can be inhabited for arbitrary exponent
data, including this local microcertificate.  A future hardening step should
split out a generic exponent-coordinate bridge and reserve the A0 name for a
global A0-data wrapper.

## Verification

Controller ran:

```text
cd lean && lake build DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

The focused build, full aggregator build, no-sorry check, and diff hygiene
check passed.  The full build emitted only unrelated pre-existing Core linter
warnings.
