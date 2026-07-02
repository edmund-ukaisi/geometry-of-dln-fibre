# Review - A2 with-following localized reverse domination base

Date: 2026-07-02.

Reviewer: `Noether the 2nd` (xhigh, read-only).

## Finding

No blocking issue found.

## Checks

- The statement correctly replaces the old global determinant-chart
  hypothesis by the endpoint patch
  `rawDetChart ∩ rawOrderOnEndpoint preimage P`.
- The conclusion is localized to `rawHaar.restrict P`, with the necessary
  hypothesis `P subset rawSourceSet` exposed explicitly.
- The proof route matches the pen-and-paper calculation: apply the
  patch-parametric raw-order COV to identify the weighted endpoint-Haar patch
  after raw-order pushforward, then transfer the weighted domination through
  `Y` and `Phi`.
- The theorem is only the `baseJ` layer.  The downstream coordinate-source
  source-density wrapper still calls the older global theorem, so a localized
  source-density wrapper remains the next target.

## Residual risk

The main notation trap is semantic rather than formal: the endpoint tuple and
the raw-order tuple share the same `RawTuple` type, so `P : Set RawTuple` must
be read as a raw-order target patch.  The theorem name `rawOrderOnEndpoint`
and the explicit preimage patch make that role visible.
