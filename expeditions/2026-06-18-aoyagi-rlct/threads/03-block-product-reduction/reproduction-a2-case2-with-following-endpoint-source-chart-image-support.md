# Reproduction - A2 Case 2 with-following endpoint source-chart image support

Date: 2026-07-02.

Status: with-following local chart-produced source-image support theorem
reproduced and formalised.  This note does not claim local `Y` change of
variables, endpoint Haar transport, source-image coverage beyond the actual
image, raw-map pushforward, normal crossings, pole order, or RLCT extraction.

## Source Boundary

Aoyagi's Case 2 selected-pivot coordinate calculation, PDF pp. 19-21, supplies
the enlarged source coordinates used here: passive-theta coordinates plus an
independent following factor.  The existing Lean source-image theorem already
produces a local open set `V` on which the enlarged endpoint source chart

```text
sourceChart z =
  case2PassiveThetaWithFollowingFactorEndpointSourceChart ... z
```

is continuous and injective, has measurable image `sourceChart '' V`, and has a
readback left inverse.  The present step records a measure-theoretic consequence
of this local image package.

## Calculation

Let `thetaMeasure` be any measure on the enlarged theta-coordinate domain, and
define

```text
mu = Measure.map sourceChart (thetaMeasure.restrict V).
```

Since `V` is open, it is measurable.  Since `sourceChart` is continuous on `V`,
it is a.e.-measurable for `thetaMeasure.restrict V`.  Also, almost every point
of `thetaMeasure.restrict V` lies in `V`.  Therefore almost every point of the
pushforward `mu` lies in the actual image `sourceChart '' V`.

Equivalently,

```text
mu.restrict (sourceChart '' V) = mu.
```

This uses only the generic image-support lemma for an a.e.-measurable map on a
restricted measurable domain.

## Checks

- The theorem is for the chart-produced measure only.
- The image is the actual local image `sourceChart '' V`; no larger source-rank
  stratum or global source image is covered.
- No density comparison, Haar transport, Jacobian formula, raw-map pushforward,
  normal-crossing calculation, pole order, or RLCT extraction is used.

The theorem is a bookkeeping socket for future source-image contracts: once a
measure is produced by the local with-following endpoint source chart, it can
be restricted to the local source-chart image without changing it.
