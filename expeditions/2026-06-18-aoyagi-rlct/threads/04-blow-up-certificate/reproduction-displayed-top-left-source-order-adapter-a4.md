# A4 Displayed Top-Left Source-Order Adapter

Status: reproduced a generic source-order handoff for the displayed top-left
selected-entry pivot calculation.

## Source Calculation

For both Case 1(2) and Case 2, Aoyagi displays the pivot
`d_(J+1,J+1)`. After the selected chart has been normalised and the pivot row
and column are put first, the local block has the form

```text
A = [ 1  y
      x  D ].
```

The displayed column operation is

```text
Q    = [ 1  -y ]
       [ 0   I ],

Q^-1 = [ 1   y ]
       [ 0   I ].
```

Then

```text
A Q = [ 1      0
        x   D - x*y ].
```

The following factor is transported by replacing `C` with `Q^-1 C`.

After row weights have been updated with the selected variable counted once,
assume quotient witnesses

```text
b_i = q_i * b_0
```

for every lower residual row. The lower-unitriangular row operation

```text
P = [ 1       0
     -q_i*x_i I ]
```

then gives

```text
(P * diag(b) * A) * C
  = (diag(b) * [1 0; 0 (D-x*y)]) * (Q^-1 C).
```

This is the common finite algebra behind the displayed top-left Case 1(2) and
Case 2 pivot calculations.

## Case Split

Case 2 is expected to instantiate this from the existing full residual-block
selected-entry substitution wrappers after a separate theorem supplies the
matching `weightedSource` equality. The source blows up the full residual
block, and existing Lean APIs already package the displayed residual block,
the top-left pivot, following-factor transport, recurrence-gap flatness, and
supplied successor weights. This note is a roadmap observation, not a proved
instantiation theorem.

Case 1(2) is different. The source divides only the row strip

```text
J+1 <= i <= J+J1,
J+1 <= j <= n_(S+1),
```

and also writes `u_(s,k)=u_(S,J+1)u'_(s,k)`. Lower residual rows outside the
strip still participate in the later `Q/P` matrix calculation. Therefore a
future Case 1(2) source wrapper must explicitly supply the weighted source
block after this factorisation; it must not use the full residual-block
selected-entry substitution as if Case 1(2) were Case 2.

## Lean Handoff

`WeightedPivotFirstSubstitutionData` records only the already transported
finite data:

- pivot row weight `b0`;
- lower row weights `b`;
- quotient witnesses `q`;
- normalised block components `x`, `y`, and `D`;
- an already weighted, already source-substituted block `weightedSource`;
- a following factor `C`;
- the equality
  `weightedSource = weightedPivotDiagonal b0 b * pivotPreQBlock x y D`;
- the quotient equation `b i = q i * b0`.

The theorem `WeightedPivotFirstSubstitutionData.sourceOrder_identity` applies
the existing finite `Q/P` algebra to this supplied data. The existential
wrapper chooses `q` from divisibility hypotheses.

## Scope

This checkpoint proves:

- a Case 1 finite-width helper deriving the displayed continuation bound from
  the first-jump row bound plus the actual column bound;
- a generic source-order adapter for an already supplied weighted pivot-first
  block;
- an existential version choosing quotient witnesses from divisibility.

It does not prove:

- construction of the selected-entry chart;
- full residual-block substitution in Case 1(2);
- affine blow-up atlas coverage;
- chart regularity or transition regularity;
- source validity of the hidden old label in Case 1;
- recurrence or exponent post-data;
- the continuation/advance transition invariant;
- polynomial-coordinate Jacobians, normal crossings, or RLCT extraction.
