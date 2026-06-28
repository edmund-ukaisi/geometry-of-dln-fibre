# Review: A2 selected-entry all-pivot nonzero coverage

Reviewer: xhigh `Boyle the 3rd`.

Verdict: PASS.

## Checks

- The center-coordinate theorem chooses a nonzero coordinate and then applies
  the existing fixed-pivot selected-entry inverse.
- The matrix theorem chooses a nonzero residual-matrix entry, sends it through
  the supplied residual-coordinate equivalence as the pivot, and delegates to
  the existing fixed-pivot matrix inverse.
- Empty-center or empty-matrix-index cases are vacuous under `value != 0` and
  `D != 0`.
- The theorem names and docstrings say finite selected-entry coverage/inverse,
  not retained-passive source production or analytic extraction.
- The reproduction and statement card preserve the same boundary.

## Nonclaims checked

The lemmas do not prove retained-passive source/readback nonzero production,
factor alignment for Aoyagi's displayed post-pivot/following factors, source
measure or prior transport, normal crossings, pole order, or RLCT.

## Verification

Focused build of `DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure` passed
with pre-existing imported linter warning noise.  Direct axiom-footprint check
for both new lemmas reports:

```text
[propext, Classical.choice, Quot.sound]
```
