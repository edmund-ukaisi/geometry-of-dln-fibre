# A4 Case 2 Displayed Center Count

Status: reproduced the displayed Case 2 residual-block coordinate count.

## Source Situation

Aoyagi's Case 2 displayed chart uses the residual block

```text
D_J = (d_ij),   J+1 <= i <= M(S),   J+1 <= j <= M^(S+1).
```

Here `M(S)` is the prefix minimum through layer `S`, while `M^(S+1)` is the
actual active width of the next layer. The displayed continuation condition is

```text
J+1 <= M(S+1) = min(M(S), M^(S+1)).
```

Under this condition, the top-left displayed pivot `(J+1,J+1)` lies in the
residual block and both residual intervals are nonempty.

## Reproduction

The selected coordinate equations in the Case 2 center are

```text
d_ij = 0
```

for all pairs in the residual block. The row interval is inclusive:

```text
J+1, J+2, ..., M(S).
```

Its size is

```text
M(S) - (J+1) + 1 = M(S) - J.
```

The column interval is also inclusive:

```text
J+1, J+2, ..., M^(S+1),
```

with size

```text
M^(S+1) - (J+1) + 1 = M^(S+1) - J.
```

Therefore the number of selected residual-block coordinates is

```text
(M(S)-J)(M^(S+1)-J).
```

This is exactly the scalar expression used by the corrected Case 2
new-label numerator package:

```text
M'_(S,J+1) = (M(S)-J)(M^(S+1)-J).
```

## Scope / Caveats

- This is a coordinate-equation count for the displayed Case 2 residual block,
  not a dimension theorem.
- The column bound is the actual width `M^(S+1)`, not the prefix minimum
  `M(S+1)`.
- The continuation hypothesis is used only to ensure the displayed chart is in
  the continuing `J -> J+1` branch and to justify the integer cardinality
  comparison without truncated subtraction.
- This count is not a Jacobian exponent. In the usual blow-up volume
  convention a Jacobian contribution would require separate chart/Jacobian
  analysis and would involve a one-less exponent.
- This does not prove chart coverage, chart-produced recurrence or exponent
  post-data, coordinate regularity, normal crossings, RLCT extraction,
  termination, or a transition invariant.
- This does not repair the printed Case 2 vector mismatch; it supports only
  the corrected prefix-minimum numerator expression already separated in the
  expedition.
