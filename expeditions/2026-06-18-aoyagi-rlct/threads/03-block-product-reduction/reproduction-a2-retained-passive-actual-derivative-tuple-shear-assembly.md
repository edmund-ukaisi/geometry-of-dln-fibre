# Reproduction - A2 retained-passive actual derivative tuple shear assembly

Date: 2026-06-27.

Status: controller pen-and-paper assembly; Lean proved; xhigh review pending.

This note is independent of the quiver-based paper.  It packages the retained-
passive raw-order component calculations already reproduced for Aoyagi's local
p.13 product-reduction chart.

## Setup

Let

```text
raw   = topologyTupleEdgeRawOrder,
data  = ofTopologyTuple z,
coord = data.toCoordinateData,
Dzv   = (D raw z)(v).
```

The formal determinant-bearing map at `z` is

```text
retainedPassiveFormalRawOrderJacobianAt z.
```

Its block formulas are the already-proved raw-order formal formulas:

```text
A1passive_p -> -A_(p+1) dF2_(p+1) - F2_(p+1) dA3_(p+1)
F2_p        -> -(A_p + F2_(p+1) A3_p) dF2_p + F2_(p+1) dC_p
A3_p        -> dA3_p
C_p         -> dC_p - A3_p dF2_p
Ctop        -> -dF2_1 A3_0 - F2_1 dA3_0 - d(Tail^{-1}) Ctop
F3          -> dF3 * (-LastTop).
```

The last two lines use the previously reproduced first-top and terminal
lower-left solves.  `Tail` is the passive top-left product after the first
edge, while `LastTop` is the one-edge terminal residual factor; for `M = 0`,
`LastTop = coord.Ctop`.

## Componentwise Sheared Tuple

Define a tuple-level correction of the actual derivative by applying the landed
component shears:

- passive `A1` components subtract the successor `F2` and `A3` variations;
- `F2` components add the raw top-left derivative times the preceding `F2` and
  subtract the successor `F2` differential times `C`;
- passive `A3` components are read directly;
- `C` components add the raw lower-left derivative times the preceding `F2`;
- `Ctop` subtracts the first successor corrections and the passive-tail inverse
  correction;
- `F3` subtracts the early lower-left tail derivative and adds the terminal
  top-factor derivative correction.

Each field is exactly one of the already-landed component bridges, so the
tuple equality follows by extensionality of the nested product tuple.

## Lean Target

The Lean package is:

```text
shearedTopologyTupleEdgeRawOrderFDerivAt
sheared_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

The proof is deliberately just product extensionality and component bridge
reuse.

## Guardrails

- This is not a proof that the actual Frechet derivative itself equals the
  formal raw-order map.
- This is not yet a determinant theorem, because the displayed correction
  package has not been factored as a staged determinant-one target-side
  `LinearEquiv`.
- This is not a change-of-variables theorem, source-prior transport, normal-
  crossing statement, pole-order theorem, or RLCT theorem.
- The determinant-relevant next step must turn these component identities into
  target-side shears whose coefficients are recovered from formal target
  coordinates, not merely paste the six component identities together.
