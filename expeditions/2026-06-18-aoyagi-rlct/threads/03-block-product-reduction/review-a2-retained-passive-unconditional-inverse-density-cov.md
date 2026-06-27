# Review - A2 Retained-Passive Unconditional Inverse-Density COV

Date: 2026-06-27.

Reviewer: Heisenberg the 4th, xhigh read-only explorer.

## Verdict

No blocking findings.

## Checks

Heisenberg reviewed the changes in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesMeasure.lean`, focusing on
the inverse-density continuity proof, a.e.-measurability discharge,
unconditional inverse-density COV wrapper, and downstream composition and
edge-family wrappers.

The review confirmed:

- the target-side reciprocal continuity uses the correct nonzero input to
  `ContinuousAt.inv0`, namely positivity of the forward determinant density at
  `invMap y0`;
- the a.e.-measurability derivations use `ContinuousOn.aemeasurable0` on the
  restricted open chart sets;
- the unconditional wrapper discharges the three former density measurability
  hypotheses before calling the conditional theorem;
- the downstream composition wrapper and edge-family specialization preserve
  measure direction and use the right absolute-continuity lift/readback
  identity;
- no overclaim beyond chart-coordinate inverse-density transport was found.

## Current Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesMeasure.lean
```

Full `DLNFibre` build passed, with pre-existing linter warnings in unrelated
files.  `scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`,
and `0 axiom`.  `git diff --check` passed.

The reviewer also ran the focused measure build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesMeasure.lean
```

It passed.  The reviewer also ran `git diff --check` and a focused forbidden
marker search over the relevant measure/topology/derivative files; both were
clean.
