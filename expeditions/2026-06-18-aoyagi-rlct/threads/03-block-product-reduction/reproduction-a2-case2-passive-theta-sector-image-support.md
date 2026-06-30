# Reproduction - A2 Case 2 passive theta sector-image support

Date: 2026-06-30.

Status: pen-and-paper check before Lean.  This is passive-sector image
bookkeeping, not Haar transport or source-prior construction.

## Question

The passive-sector construction note says the next measure theorem must name
the image sector

```text
case2PassiveThetaEndpointTopologyTuple '' thetaDomain.
```

Can we first name this sector and prove that the pushforward of any theta
measure restricted to `thetaDomain` is supported on it?

Answer: yes.  This is a tautological but useful support theorem.  It is not
the desired exact or dominated sector-measure comparison, but it gives that
future comparison a named target set.

## Setup

Let

```text
Y theta =
  case2PassiveThetaEndpointTopologyTuple n hS hcont hnext theta eNext e
```

and let `Omega` be a theta-domain sector, for example a local determinant and
nonzero-pivot sector or a later small-box passive sector.  Define

```text
case2PassiveThetaEndpointSectorSet Omega = Y '' Omega.
```

For a theta-domain measure `thetaMeasure`, consider the restricted pushforward

```text
nu = Measure.map Y (thetaMeasure.restrict Omega).
```

## Calculation

Assume `Omega` is measurable.  Then

```text
theta in Omega
```

holds for `thetaMeasure.restrict Omega`-almost every `theta`.  Therefore

```text
Y theta in Y '' Omega
```

holds for `thetaMeasure.restrict Omega`-almost every `theta`.  If `Y` is
a.e.-measurable for the restricted measure and the image sector is measurable,
`ae_map_iff` transports this to

```text
for nu-almost every y, y in case2PassiveThetaEndpointSectorSet Omega.
```

Consequently

```text
nu.restrict (case2PassiveThetaEndpointSectorSet Omega) = nu.
```

The measurability of the image sector is kept as an explicit hypothesis.  It
should not be hidden: later exact sector transport will also need a measurable
target sector.

## Lean Target

Add the sector-set names to

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSector.lean
```

and the support theorem to

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Suggested public names:

```text
case2PassiveThetaSectorSet
case2PassiveThetaEndpointSectorSet
measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_eq_self
```

## Nonclaims

This slice does not prove exact passive-sector Haar transport, determinant
chart Haar transport, a bounded-density or finite-scalar domination theorem,
source-image equality, source-rank coverage, an original source prior,
normal crossings, pole order, or RLCT extraction.  It only names the sector
image and proves support of a restricted chart-produced pushforward on that
image.
