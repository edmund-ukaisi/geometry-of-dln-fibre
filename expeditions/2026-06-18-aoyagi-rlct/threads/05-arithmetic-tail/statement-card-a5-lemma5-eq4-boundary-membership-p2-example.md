# Statement card - A5 Lemma 5 equation (4) p=2 boundary membership example

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Name:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_p2_constantWidth_example`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_p2_constantWidth_sourceSelected_example`

## Statement

Lean records a concrete constant-width guardrail example:

```text
ell=5, a=4, p=2, M=5, all selected widths W_i=4.
```

For any supplied equation `(4)` piecewise certificate with these constants,
the strict boundary value belongs to its boundary-coordinate interval.

## Proved

- The boundary-coordinate width window is satisfied at `p=2`.
- A supplied equation `(4)` certificate therefore gives boundary-coordinate
  membership.
- The concrete selected-width tuple satisfies the selected-width sum and
  strict selected-width inequalities from Definition 3.

## Assumed

- For the membership conclusion, a supplied equation `(4)` piecewise branch
  certificate for the concrete constants.

## Reproduced Arithmetic

- The selected-width sum and strict selected-width inequalities are compatible
  with the example arithmetic recorded in the reproduction note.

## Cited

- None in Lean. This is finite integer and interval arithmetic.

## Deferred

- Construction or existence of equation `(4)`'s supplied certificate.
- Construction of equation `(4)`'s displayed vector.
- Terminal `tilde t=0`.
- Case 1(2) chart sequence, introduced-label status, vector admissibility,
  Lemma 5 order count, normal crossings, and RLCT extraction.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector`
- `lake env lean DLNFibre.lean`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
