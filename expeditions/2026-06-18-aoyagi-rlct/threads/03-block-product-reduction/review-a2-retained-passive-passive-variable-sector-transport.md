# Review - A2 Retained-Passive Passive-Variable Sector Transport

Date: 2026-06-29.

Status: PASS after minor wording repairs.

Reviewed artifacts:

```text
reproduction-a2-retained-passive-passive-variable-sector-transport.md
statement-card-a2-retained-passive-passive-variable-sector-transport.md
```

## Reviewers

`Linnaeus the 3rd`, xhigh read-only source/math review, returned PASS.
The review checked Aoyagi pp. 10-13 by `pdftotext` and found no source-fidelity
blocker.  It confirmed:

- Lemma 2 is reproduced with
  `F2 = -A1^{-1} A2`, `F3 = -A3 A1^{-1}`, and
  `C4 = -A3 A1^{-1} A2 + A4`.
- The Theorem 3 induction step is reproduced with
  `C^(S+1) = -A3' (A1')^{-1} A2' + A4'`,
  `F2'' = -(A1')^{-1} A2'`, and
  `F3'' = F3' - (prod_{s=1}^S C^(s)) A3' (C1' A1')^{-1}`.
- The p.13 lower-right product-difference block is kept as
  `prod_s C^(s) - F3 F2`, not `prod_s C^(s)`.
- The regular/residual distinction is correct: `C1 - Er`, `F2`, and `F3`
  are regular variables, while the corrected lower-right block is residual.
- The measure/prior language does not claim passive-sector Haar transport or
  an external/original source-prior comparison from Aoyagi pp. 10-13.

`Halley the 3rd`, xhigh read-only Lean/API review, returned PASS.  It confirmed
that the named Lean inputs exist or have direct exact matches and that the
chart-produced/Haar/source-prior separation matches the current Lean frontier.
It also found two nonblocking precision points:

- The raw passive variables in the constructor are typed over
  `case2PostPivotTwoEdgeDomain ...`; endpoint equivalences then move them to
  `throughSubspaceEndpointComplementIndex ...`.  The reproduction note was
  repaired to distinguish `kappaRaw` from `kappaEnd`.
- The proposed next implementation should cite the already-present passive
  pointwise residual readout theorem
  `paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive`
  or its underlying residual-factor identity, not only source-readback plus
  `preimageOfPivotNeZero_chartMap`.  The reproduction and card were repaired
  to state the next target as a combined with-passive open punctured-sector
  packaging theorem.

## Verdict

The artifacts are accepted as a controller frontier/specification, not as a
Lean theorem.  The next Lean theorem in this lane should be a passive-variable
open-sector inverse/readout package, or else a fully specified
passive-variable sector measure theorem with concrete domain, sector image,
target measure, and Jacobian fields.  No passive-sector Haar transport,
external source-prior comparison, selected-entry source-image equality,
source-rank coverage, normal crossings, pole order, or RLCT extraction is
claimed here.
