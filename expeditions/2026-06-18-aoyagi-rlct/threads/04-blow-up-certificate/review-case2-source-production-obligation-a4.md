# Review - Case 2 Source Production Obligation

Date: 2026-06-22.

Reviewers: Beauvoir and Planck, xhigh effort.

Verdict: pass as a supplied interface, with one naming hardening applied.

2026-06-22 API update: this review describes the earlier interface that still
had a supplied next chart-family field.  That field has since been removed
after the true-predicate audit; the live `SourceProductionObligation` no
longer contains `continuing_suppliedNextChartFamily`.

## Findings

Both reviewers agreed that the next Lean artifact may be a `Prop`-valued
obligation/interface, not a theorem constructing source production from the
current displayed chart boundary.  The name must include `Obligation` or
otherwise signal supplied data; it must not read as a production theorem.

The accepted branch separation is:

- continuing branch under `J+2 <= prefixMinNat n (S+1)`;
- actual-width stopped branch under `n(S+1)=J+1`;
- row-exhausted stopped branch under `prefixMinNat n S=J+1`.

The reviewers specifically required that actual-width terminal rows and
row-exhausted transported rows stay separate, and that row-exhausted data not
receive `(S+1,0)` relabelled certificates unless actual width is separately
supplied.

## Applied Hardening

In the historical interface, the continuing next chart-family field was
renamed from
`continuing_nextChartFamily` to `continuing_suppliedNextChartFamily`, so the
field could not be read as a chart-family construction from the current data.
The field is now removed from the live API.

## Residual Boundary

The structure has no `of_...` constructor from
`Case2DisplayedSuppliedChartFamilyBoundary`.  It does not make stopped
branches exclusive and does not include Jacobian, normal-crossing, pole-order,
RLCT, termination, or quiver content.
