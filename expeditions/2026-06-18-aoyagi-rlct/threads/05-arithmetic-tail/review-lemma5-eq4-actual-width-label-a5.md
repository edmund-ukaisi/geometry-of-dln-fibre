# Review - Lemma 5 equation (4) actual-width label

Reviewer: xhigh `Ohm`.

Status: passed.

## Scope

This review covers:

```text
aoyagiLemma5Eq4_actualWidthLabel_of_widthCompatibility
```

## Findings

No blocking findings.

The theorem is appropriately conditional.  It proves only
`actualWidthLabel L n (C.point p - 1) k`, and it keeps all bridges explicit:

- Definition 3 selected-width arithmetic is supplied by `hselected` and
  `hsource`.
- Source-layer range is supplied by `hs_pos` and `hs_le`.
- Width compatibility is supplied by `hwidth`.
- Nat/Int label compatibility is supplied by `hk`.

The cast proof derives integer bounds first and then casts to natural-number
bounds.  No import cycle was found.

The theorem name was adjusted after review from
`aoyagiLemma5Eq4_actualWidthLabel_of_selectedWidth` to
`aoyagiLemma5Eq4_actualWidthLabel_of_widthCompatibility`, so the explicit
width-compatibility hypothesis is visible at the API boundary.

## Verification

Reviewer reported:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
lake env lean DLNFibre.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
lake build DLNFibre
```
