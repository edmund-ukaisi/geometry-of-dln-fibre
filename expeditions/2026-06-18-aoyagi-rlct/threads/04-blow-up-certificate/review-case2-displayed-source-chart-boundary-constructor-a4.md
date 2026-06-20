# Review - A4 Case 2 Displayed Source-Chart Boundary Constructor

## Pre-Implementation Scouts

- Source/math scout: `Mill the 4th`, xhigh.
- Lean/API scout: `Avicenna the 4th`, xhigh.

Both scouts recommended treating this as a narrow source-facing constructor
only: it should package the displayed supplied boundary with scalar equal to
the displayed source chart pivot value, while avoiding chart-production,
coverage, Jacobian, or exponent-production claims.

## Post-Implementation Reviewers

- Source/math reviewer: `Herschel the 4th`, xhigh.
- Lean/API reviewer: `Mendel the 4th`, xhigh.

## Findings

No source/math fidelity defect was found.  The checkpoint is correctly scoped
as source-chart-pivot supplied-boundary packaging: the boundary scalar is
written as the displayed source chart pivot value, the post recurrence state is
`pre.case2Succ` of that same value, and the corrected exponent post-data remain
the supplied selected-label overrides.  The documentation explicitly excludes
chart production, atlas coverage, coordinate-derived regularity,
Jacobian/volume arithmetic, normal crossings/RLCT, transition invariance, and
printed-vector repair.

The Lean/API reviewer found no medium or high defect.  Two low findings were
addressed before commit:

- The first implementation duplicated the fields of
  `Case2DisplayedSuppliedChartFamilyBoundary.of_case2Succ_updateSelected`.
  The theorem is now a wrapper over that existing constructor, reducing API
  drift risk.
- The statement card originally said the scalar was "not an arbitrary
  parameter `u`."  Since the theorem still quantifies `u : R` and the
  displayed pivot simplifies to `u`, the wording now says the scalar is
  syntactically exposed as the displayed source chart value.

## Verification

- `git diff --check`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`

## Residual Risk

This checkpoint intentionally depends on the fact that the displayed source
chart pivot value is definitionally the selected scalar `u`.  It does not show
that all coordinates in Aoyagi's affine chart produce the recurrence state or
the corrected exponent post-data, and it does not touch Jacobian/volume data,
coverage, normal crossings, RLCT extraction, termination, transition
invariance, or the printed Case 2 vector mismatch.
