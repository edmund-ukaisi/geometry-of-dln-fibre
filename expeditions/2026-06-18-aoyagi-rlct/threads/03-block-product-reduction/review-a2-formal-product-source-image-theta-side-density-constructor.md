# Review - A2 formal-product/source-image theta-side density constructor

Date: 2026-07-02.

Reviewer: xhigh read-only audit `Singer the 2nd`.

## Verdict

Pass after two low-severity fixes.  The new helper and constructor are pure
measure bookkeeping.  They do not prove an Aoyagi Jacobian formula, a density
bound, a formal-product/source-image comparison, Haar transport, normal
crossings, pole order, or RLCT extraction.

## Findings And Fixes

- The equality helper originally inherited ambient topology assumptions from
  the namespace variable block.  This was only a reusability issue, not a
  mathematical overclaim.  Fixed by moving the helper before the topology
  variable block and giving it only `[MeasurableSpace Theta]` and
  `[MeasurableSpace E]`.
- The statement card named
  `measure_map_restrict_withDensity_eq_withDensity_map_of_ae_eq` without its
  module.  Fixed by recording
  `lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean`.

## Scope Check

The reviewer confirmed that:

- the theta-side equality remains a hypothesis;
- the factorization
  `theta => density (sourceChart theta)` is definitional;
- the only substantive proof step is the existing pushforward-with-density
  lemma from `LocalMeasureHandoff.lean`;
- the constructor fills the contract fields directly after converting the
  equality, and the density bound remains a hypothesis.

## Nonclaims

No Jacobian density is constructed.  No density bound is proved.  No
formal-product/source-image domination follows without the supplied equality
and bound.  No raw-Haar transport, determinant-chart Haar equality,
source-image coverage, original prior transport, normal crossings, pole order,
or RLCT extraction is proved.
