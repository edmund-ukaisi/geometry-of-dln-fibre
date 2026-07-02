# Review - A2 with-following localized source-density raw domination

Date: 2026-07-02.

Reviewer: `Hubble the 2nd` (xhigh, read-only).

## Finding

No blocking issue found.

## Checks

- The localized source-density theorem mirrors the existing global wrapper but
  replaces the global base theorem with the patch-parametric base theorem.
- The callback correctly quantifies over a caller-chosen raw-order patch
  `P : Set RawTuple`, keeps `P subset rawSourceSet` explicit, and requires
  null-measurability of the endpoint patch
  `rawDetChart ∩ rawOrderOnEndpoint preimage P`.
- The lower-density adapter is used with `target := rawHaar.restrict P`, so
  the density argument remains the same measure-theoretic calculation as in
  the global theorem.
- The eventual wrapper shrinks into the source-density lower-bound
  neighborhood and forwards `hP`, endpoint-patch null measurability, and
  endpoint-patch domination to the localized source-density theorem.

## Residual Risk

This is still conditional.  It does not construct the endpoint-patch
domination or prove positivity/lower bounds for the source density; it only
localizes the already conditional handoff from `rawSourceSet` to a supplied
raw-order patch.
