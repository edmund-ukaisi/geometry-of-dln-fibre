# Reproduction - A2 selected-entry source-chart coverage boundary

Date: 2026-06-25.

Status: controller reproduction after xhigh source/API scouting.  This is a
boundary checkpoint before further Lean work on the selected-entry local
source-stratum endpoint.

## Source Anchor

Aoyagi PDF pp. 15-18, Case 1 (2), and pp. 19-21, Case 2.

The relevant source text is in the recursive blow-up proof, not in the p.13
regular-coordinate reduction itself.  In both places Aoyagi says to construct a
blow-up along a residual-block center and then treats "instances" in which the
top-left residual entry is selected:

```text
d_(J+1,J+1) = u_(S,J+1),
d_ij = u_(S,J+1) d'_ij for the displayed off-pivot entries.
```

In Case 1 (2), the displayed center block only includes rows
`J+1,...,J+J_1`; the lower rows reappear afterward in the full `D_J''` matrix.
In Case 2, the same top-left selected-entry pattern is applied to the full
residual block.

## Pen-And-Paper Check

Let `E` be the normalized displayed matrix after the selected-entry
substitution.  Its first row is

```text
(1, d'_(J+1,J+2), ..., d'_(J+1,M(S+1))).
```

Aoyagi then multiplies on the right by the unipotent matrix

```text
Q =
[ 1  -d'_(J+1,J+2)  ...  -d'_(J+1,M(S+1))
  0   1              ...   0
  ...
  0   0              ...   1 ].
```

Therefore `D_J'' = E Q` has first row `(1,0,...,0)`, and for lower rows
`i > J+1` and columns `j > J+1`,

```text
d''_ij = E_ij - E_i,(J+1) d'_(J+1),j.
```

The displayed row operation matrix `P` then clears the first column and leaves
a lower-right residual block `D_(J+1)`.  Thus the elementary residual
coordinate content of the selected-entry chart is the Schur-type formula

```text
(D_(J+1))_ij = E_ij - E_i,(J+1) d'_(J+1),j.
```

This calculation is independent of the p.13 local source-stratum equality.  It
is finite matrix algebra inside the displayed top-left affine chart.

## Coverage Boundary

Aoyagi does not write a finite affine cover of the blow-up center here.  The
printed proof does not enumerate charts for every possible residual pivot, does
not choose a maximal coordinate sector, and does not analyse chart overlaps.
It only displays the top-left selected-entry chart.

Consequently the current Lean endpoint must keep source coverage explicit:

```text
Ulocal ∩ sourceStratum =
Ulocal ∩ chartMap pivot '' signedBoxSet Rres
```

is not discharged by the printed selected-entry calculation.

## Lean Consequence

The remaining selected-entry residual hypothesis

```text
∀ y,
  aoyagiCoordinateSquareSum
    (paperEndpointFixedBaseResidualBlockCoordinateMap ... (chartMap pivot y))
  = CenterCoord.residual pivot y
```

is not provable for arbitrary `CedgeBase`.  Aoyagi's displayed calculation can
support an exact residual-square-sum theorem only after a coordinate-readout
bridge identifies each fixed-base residual block coordinate with a
selected-entry chart coordinate, up to a finite reindexing.

The smallest honest Lean target is therefore:

1. prove the elementary center-coordinate identity
   `CenterCoord.residual pivot y = aoyagiCoordinateSquareSum (chartMap pivot y)`;
2. prove a square-sum transport theorem from an explicit equivalence between
   fixed-base residual indices and selected-entry center coordinates, plus
   pointwise coordinate readout;
3. keep source image/coverage as supplied unless a later source reproduction
   constructs an actual analytic atlas or finite cover.

## Kill Conditions

- Do not claim the top-left chart covers the residual blow-up center.
- Do not infer all-pivot coverage from the finite selected-entry certificate.
- Do not use the residual square-sum bridge without a concrete coordinate
  readout theorem or an explicit replacement lower-bound hypothesis.
- Do not formalise the printed weighted equality as written without fixing the
  `u_(S,J+1)` convention; the source text writes both new `b'_i` factors and an
  external `u_(S,J+1)` factor.
