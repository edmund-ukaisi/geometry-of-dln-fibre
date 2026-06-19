# Statement card - A4 selected-label update data

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `a0a9a49`.

Names:

- `DLNFibre.DLN.Aoyagi.updateSelectedLabelVector`
- `DLNFibre.DLN.Aoyagi.updateSelectedLabelVector_selected`
- `DLNFibre.DLN.Aoyagi.updateSelectedLabelVector_of_ne`
- `DLNFibre.DLN.Aoyagi.updateSelectedLabelScalar`
- `DLNFibre.DLN.Aoyagi.updateSelectedLabelScalar_selected`
- `DLNFibre.DLN.Aoyagi.updateSelectedLabelScalar_of_ne`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.case1_selectedLowerTail_updateData`

## Statement

Lean defines total post-assignment functions by overriding one selected label
`(s0,k0)` and leaving every other label unchanged:

```text
vector assignment: t'(s0,k0) = new vector,
scalar assignment: a'(s0,k0) = new scalar.
```

The convenience theorem instantiates the conditional Case 1 same-domain update
with these overrides. It replaces the selected vector by
`lowerTailVector`, replaces the selected numerator by the actual-width
increment, and replaces the selected least value by `J`.

## Source role

This removes mechanical post-data hypotheses from the Case 1(1) certificate
bookkeeping theorem. It is a syntactic assignment override, not a source
construction. Values outside the introduced-label domain are formal and
irrelevant to the certificate.

## Proved

- The vector override has the selected value at `(s0,k0)`.
- The vector override is unchanged at labels different from `(s0,k0)`.
- The scalar override has the selected value at `(s0,k0)`.
- The scalar override is unchanged at labels different from `(s0,k0)`.
- The Case 1 same-domain lower-tail certificate update applies directly to
  these override functions.

## Not proved

- No new source geometry beyond the previous same-domain update theorem.
- No proof that a chart produces these assignment overrides.
- No finite-map domain theorem; these are total functions.
- No construction or existence theorem for the selected label.
- No proof of `leastValue = level` or `FlatTailFromPred`.
- No row-strip division, `b'_i` recurrence bookkeeping, Jacobian, ideal
  equality, chart coverage, transition invariant, domain advancement,
  normal-crossing certificate, or RLCT extraction.

## Status

- Sorry-free and xhigh source-scope reviewed at `a0a9a49`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
