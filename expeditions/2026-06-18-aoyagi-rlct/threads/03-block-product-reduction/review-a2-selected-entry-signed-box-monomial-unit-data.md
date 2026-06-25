# Review - A2 selected-entry signed-box monomial-unit data

Date: 2026-06-25.

## Independent Inputs

Two xhigh read-only scouts informed this slice:

- Lean/API scout `Dewey the 6th`: recommended a selected-entry signed-box
  adapter, warned against using the raw signed Jacobian determinant as a
  nonnegative density when the exponent is odd, and identified the existing
  signed-box monomial-unit consumer as the target API.
- Source/math scout `Locke the 6th`: confirmed the reproducible calculation is
  exactly the selected-entry square-sum and formal pivot-first determinant, and
  listed chart coverage, source production, pushforward, and analytic density
  transport as still outside the calculation.

## Verdict

Accepted at the stated scope.

The Lean bridge proves concrete signed-box monomial-unit data for the
selected-entry chart coordinates.  It uses the absolute formal determinant
`|u|^(|E|-1)` as the formal source-density model and separately records its
equality to the absolute value of the formal pivot-first determinant.  This
matches the measure consumer's nonnegative density expectations and avoids
overclaiming an analytic Jacobian or transported density theorem.

## Checks

The residual identity is pointwise:

```text
residual = residualUnit * prod_i |z_i|^(2*k_i).
```

The source-density identity is pointwise:

```text
sourceDensity = densityUnit * prod_i |z_i|^h_i.
```

The unit bounds are pointwise:

```text
1 <= residualUnit,
0 <= densityUnit,
densityUnit <= 1.
```

The a.e. theorem only lifts these pointwise statements to an arbitrary signed
box and applies the existing monomial-unit inequality consumer.  It does not
insert a chart map into the source measure.

## Risks

The signed-box coordinate index `Option {i // i in center.erase pivot}` is the
natural one-pivot coordinate space for the concrete bridge.  The file also
provides `SelectedEntrySignedBox.CenterCoord.*`, restating the same data over
the center subtype with zero exponents away from the pivot.  The latter is a
downstream API convenience, not a new analytic claim.

The theorem remains only a formal selected-entry density package.  A future
local chart theorem must still prove the actual pushforward and density
identity before it can feed the local-source finite-integral continuation.
