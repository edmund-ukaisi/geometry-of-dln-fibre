# Review - A2 p.13 product-coordinate left-step raw preimage

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Fermat the 2nd`.

## Scope

Review the current p.13 bridge from the constructed multi-edge
product-coordinate matrix family to the explicit raw preimage tuple, focusing
on formalisation fidelity, mathematical accuracy, and overclaiming.

Files reviewed:

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean`
- `reproduction-a2-p13-product-coordinate-left-step-raw-preimage.md`

## Findings

No high- or medium-severity issues were found.

Low issue 1: the new constructor was originally named and documented as an
`EdgeFamily`, but its type is a matrix family `∀ p, Matrix ...`, not the
realised continuous reverse-edge family used elsewhere.

Response: renamed it to
`paperEndpointFixedBaseP13ProductCoordinateMatrixFamily` and adjusted the
nearby comments and expedition notes.

Low issue 2: the reproduction note still read like a pre-implementation target
and had stale theorem-name wording.

Response: changed its status to `Lean proved`, replaced the target section by
`Lean Artifacts`, and listed the actual Lean names.

## Verdict

Passed after the two low wording/name repairs.

The proof matches the pen-and-paper calculation: it proves the tail suffix
fields, explicitly relates `S.D` back to the fixed-base residual product, uses
no inverse of `Dtail` or passive residual factors, and adds only the
`det Ctop` unit hypothesis for the raw-order target theorem.

## Nonclaims

This review did not treat the result as source coverage, measure pushforward,
signed-box density identification, normal crossings, pole order, or RLCT.
