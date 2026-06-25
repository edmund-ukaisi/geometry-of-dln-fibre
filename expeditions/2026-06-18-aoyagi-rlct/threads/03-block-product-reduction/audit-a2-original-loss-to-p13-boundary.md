# Audit - A2 original loss to p.13 boundary

Date: 2026-06-25.

Auditor: xhigh `Lagrange the 5th`, read-only.

## Verdict

The original DLN/statistical loss to p. 13 coordinate bridge was not proved at
the time of this audit.  It is now partially superseded for the concrete
square-Frobenius `lossDLN` on chain-map tuples: the endpoint basis bridge and
source-filter self-base theorem prove that specific finite comparison.

For a generic loss, statistical/KL loss, covariance-weighted loss, or product
chart statement not literally in the chain-map `lossDLN` form, the safe theorem
boundary remains conditional: assume explicitly that, eventually on the
fixed-base source-rank `nhdsWithin` filter,

```text
c0 * adaptedProductDifferenceSquareSum(x) <= originalLoss(x)
```

for some `c0 > 0`.  Under that hypothesis, the existing p. 13 finite machinery
can transfer the positive lower bound from `adaptedProductDifferenceSquareSum`
to `originalLoss` and then to the cleaned
`regularSquareSum + residualSquareSum`.

## Already In Lean

- `lossDLN` is the Frobenius square loss.  It is now connected to p. 13
  fixed-base endpoint coordinates for chain-map tuples through
  `EndpointLossComparison`; this does not cover arbitrary tuples or
  statistical/covariance losses.
- The fixed-base endpoint coordinate and determinant-chart persistence
  machinery is formalised, but it does not prove source-rank openness or a
  global Aoyagi chart theorem.
- The literal and cleaned p. 13 square-sums are locally compared by factor `2`,
  including the half lower-bound form.
- The current self-base comparison now has an original square-Frobenius
  `lossDLN` corollary for `chainMapMatrixTuple b (Cedge x)`, but only as a
  one-parameter source-filter theorem.

## Elementary But Still Unformalised

- If the target is statistical KL/prediction loss rather than Frobenius square
  loss, an input covariance/noise lower-bound comparison.
- Product-coordinate versions with an independent regular fiber variable still
  need the chart/loss-identification hypotheses used by the local-measure
  front ends.

## Boundary

Do not state `c * literal <= loss` or `c * cleaned <= loss` for a generic loss
as source-backed by Aoyagi p. 13.  Such a theorem must either prove or
explicitly assume the metric/covariance/basis bridge.  For concrete
square-Frobenius `lossDLN`, use the already-proved chain-map endpoint bridge
and keep its tuple/target-basis hypotheses visible.

## Source Audit Addendum - pp. 5-14

Aoyagi p. 8 states the Gaussian DLN setup and then says the model's
`lambda` and `theta` correspond to the LCT and order of the squared Frobenius
product residual

```text
|| prod_s A^(s) - prod_s A*^(s) ||^2.
```

The inspected source does not prove the full analytic/probabilistic passage
from the Kullback function on pp. 5-6 to this Frobenius residual for arbitrary
input covariance.  Treat that correspondence as supplied/cited unless a
separate local covariance/noise comparison is formalised.

Aoyagi p. 13 does give the elementary block calculation after the Frobenius
product residual has already been adopted:

```text
P1 (prod_s A^(s) - [E_r 0; 0 0]) P2
  = [C1 - E_r   -F2
     -F3        prod_s C^(s) - F3 F2].
```

The elementary formalisation content here is the finite block algebra and the
ideal/square-sum comparison that the `F3 F2` term is controlled by the regular
variables `F2` and `F3`.  The already-landed product-coordinate lower-bound
theorems formalise this at the fixed-base square-sum level.

Aoyagi p. 13 then states the RLCT shift

```text
(-r^2 + r(H(1)+H(L+1))) / 2
```

plus the reduced product RLCT.  The finite variable count

```text
r^2 + r(H(1)-r) + r(H(L+1)-r)
  = -r^2 + r(H(1)+H(L+1))
```

is elementary and already represented by the regular-coordinate count layer.
The analytic rule turning regular square variables into an RLCT shift remains
outside this audit's proved boundary unless supplied through the cited
normal-crossing extraction interface.

Aoyagi p. 14 invokes Theorem 4 to set `r^(s)=r` without loss of generality.
Do not treat this as elementary rank algebra.  It remains a deepest-singular
point input unless separately reproduced.
