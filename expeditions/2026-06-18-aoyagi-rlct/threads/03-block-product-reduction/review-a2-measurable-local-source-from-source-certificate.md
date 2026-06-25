# Review - A2 measurable local source from source certificate

Date: 2026-06-25.

## Verdict

Accepted at source-packaging scope.

The Lean statements extract a concrete measurable local source from an existing
fixed-base local source certificate, then expose the same package at the
regular-coordinate source-data level with the filter equality needed by the
local-source finite-integral sockets.  The proof is elementary neighborhood and
measurability bookkeeping.

## Independent Audit Inputs

The source-fidelity audit recommended a narrow target:

- construct `source = U inter sourceRankStratum`;
- prove measurability, `x0 in source`, and `source subset sourceRankStratum`;
- carry the canonical source-rank conclusion on that local source;
- do not treat p.13 as a Jacobian, pushforward, or monomial-unit theorem.

The Lean frontier audit recommended adding the source-data wrapper in
`RegularSuspensionLocalMeasure.lean`, deriving source-rank-stratum
measurability from fixed-base edge-matrix measurability and recording

```text
nhdsWithin x0 source = nhdsWithin x0 sourceRankStratum.
```

The landed theorem follows that recommendation.

## Scope Checks

- The source-rank stratum is not proved open.
- Measurability is obtained either as an explicit hypothesis or from the
  existing edge-matrix rank-stratum theorem.
- Nonvacuity is local only: the returned `source` contains the basepoint `x0`.
- The canonical source-rank conclusion is inherited from the existing
  certificate; no new block-product algebra is introduced.
- The source-data wrapper uses only `sourceData.localSourceCertificate` and the
  existing rank-stratum measurability API.

## Risks and Use Guidance

This theorem should be used to connect source-stratum-local p.13 lower bounds
to later local-source chart packages.  It should not be used as if it were a
chart image theorem: no coordinates on `source`, no signed-box map, and no
measure transport are produced here.

The next real A2 frontier remains the chart-side source work: local residual
signed-box chart/source coverage, weighted pushforward and Jacobian/source
density identity, and concrete residual/source-density monomial-unit
identities.

## Nonclaims

No signed-box chart, source chart coverage, pushforward theorem,
Jacobian/source-density formula, residual/source-density monomial-unit
production, normal-crossing extraction, pole-order computation, or RLCT theorem
is proved.
