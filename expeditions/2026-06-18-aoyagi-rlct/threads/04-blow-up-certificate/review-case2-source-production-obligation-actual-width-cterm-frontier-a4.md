# Review - Case 2 Source-Production Obligation Actual-Width Cterm Frontier

Date: 2026-06-22.

Reviewers: controller; xhigh scout `Boole the 2nd`.

## Verdict

Accepted as a narrow supplied-obligation consumer.  It fills the actual-width
stopped analogue of the existing row-exhausted supplied-`Cterm` wrapper.

## Source/Fidelity Check

The theorem consumes only data already present in `SourceProductionObligation`.
The actual-width branch hypothesis is explicit as `hwidth : n(S+1)=J+1`.
The supplied terminal matrix `Cterm` is not constructed; it is merely used via
the supplied field `actualWidth_Cterm_eq`.

The source suffix remains the supplied

```text
sourceSuffixProduct κ Ctail S hSuffix.
```

## Kill Conditions Checked

- Actual-width exhaustion is not conflated with row exhaustion.
- The payload does not claim a successor chart family or suffix production.
- Level and exponent fields are carried unchanged from the existing frontier.
- No normal-crossing, pole-order, termination, or RLCT consequence is stated.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
```
