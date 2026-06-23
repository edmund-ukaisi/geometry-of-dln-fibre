# Reproduction - A4 Case 2 continuing reindexed source-chart certificate

Date: 2026-06-23.

Status: reproduced, formalised, and xhigh-reviewed.

Review: `review-case2-continuing-reindexed-source-chart-certificate-a4.md`.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  The displayed chart chooses the top-left
residual-block pivot `(J+1,J+1)` and writes the selected-entry substitution

```text
d_{J+1,J+1} = u_{S,J+1},
d_{i,j} = u_{S,J+1} d'_{i,j}
```

for the other residual-block entries.  The paper then uses regular matrices
`Q` and `P`, defines `C'_J^(S+1) = Q^-1 C_J^(S+1)`, and rewrites the displayed
product through

```text
D'''_J = [1 0; 0 D_{J+1}].
```

Under the continuing guard `J+1 <= M(S+1)`, this is read as the same-stage
step with `J` increased by one.  The stronger guard
`J+2 <= M(S+1)` makes the next residual center nonempty.

## Local Certificate

The new Lean structure is:

```text
Case2DisplayedContinuingReindexedSourceChartCertificate
```

It packages the data we can prove locally from the displayed source chart:

- membership of the displayed pivot in the residual-block center;
- pivot and off-pivot formulas for `case2DisplayedSourceChartMap`;
- membership of the selected value `u` among transformed center values;
- divisibility of every transformed center value by `u`;
- finite center principalization
  `span(transformed center values) = span({u})`;
- the corrected post-weight convention
  `post.weight i = upivot * pre.weight i` for `J+1 <= i`;
- nonemptiness of the next residual center under the continuing guard;
- the reindexed next same-stage source-product identity, with an existential
  row-operation witness `q`;
- corrected exponent, level, least-value-gap, and recurrence-gap post-data;
- the equality between the corrected new numerator and the residual-block
  center cardinality.

The reindexed product equality is abbreviated as:

```text
Case2DisplayedReindexedNextSourceProductEq
```

This is exactly the matrix equality produced by
`sourceChartMap_reindexedNextSourceProduct_withCorrectedPostData`, with the
row-operation witness named explicitly.

## Constructor

The constructor is:

```text
sourceChartMap_continuingReindexedSourceChartCertificate
```

Inputs:

- stage hypotheses `1 <= S` and `S <= L`;
- displayed continuation `J+1 <= prefixMinNat n (S+1)`;
- continuing nonemptiness guard `J+2 <= prefixMinNat n (S+1)`;
- the pre-state exponent certificates, level invariants, and least-value gap;
- a supplied current residual-block chart-family boundary;
- a source following factor `C`.

The proof combines existing facts:

- displayed pivot membership;
- source-chart pivot/off-pivot formulas;
- finite center value membership, divisibility, and principalization;
- `case2DisplayedPostPivotResidualBlock_nonempty_of_next`;
- `sourceChartMap_reindexedNextSourceProduct_withCorrectedPostData`;
- `correctedCase2NewLabelNumerator_eq_card_of_cont`;
- recurrence post-weight update through `pre.case2Succ`.

## Corrected Weight Convention

Aoyagi p. 20 prints `b'_i = u_{S,J+1} b_i`, while p. 21 later displays an
additional outside factor `u_{S,J+1} diag(b') ...`.  These lines are not
simultaneously literal.  This certificate follows the corrected post-state
convention:

```text
post.weight i = u_{S,J+1} * pre.weight i.
```

It must not be combined with a second literal outside factor of `u` on the
same post weights.

## Boundary

This is an A4-local certificate.  It is not an
`AoyagiNormalCrossingChartCertificate`; it does not include loss or
Jacobian-prior monomial identities, unit factors, analytic chart coverage,
transition regularity for a successor atlas, source production of `Csucc`,
source suffix production, terminal source production, pole order, or RLCT
extraction.

The A0 normal-crossing extension remains a later supplied structure with
actual monomial/unit fields, not a consequence of this local certificate.

## Lean Names

```text
Case2DisplayedReindexedNextSourceProductEq
Case2DisplayedContinuingReindexedSourceChartCertificate
sourceChartMap_continuingReindexedSourceChartCertificate
```

## Kill Conditions

- Do not use this as source production of full `C'^(S+1)`.
- Do not infer chart coverage or transition regularity for successor charts.
- Do not feed it directly into A0 without supplied loss/Jacobian monomial
  identities and unit fields.
- Do not double-count the printed outside `u` factor.
