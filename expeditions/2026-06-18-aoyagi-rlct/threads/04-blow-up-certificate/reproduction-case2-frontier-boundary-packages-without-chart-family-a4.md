# Pen-and-paper reproduction - A4 Case 2 frontier packages without chart-family input

Status: reproduced for a finite API-hardening slice.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  The displayed pivot chart at
`(J+1,J+1)` gives the source substitution

```text
d_(J+1,J+1) = u,
d_ij = u * residual_ij  for every other residual-block center entry.
```

The finite frontier alternatives after this pivot are the same ones recorded
in the previous source-chart frontier package:

- continuing same-stage branch `J+2 <= M(S+1)`;
- actual-width stopped branch `M^(S+1)=J+1`;
- current-prefix row-exhausted branch `M(S)=J+1`.

These alternatives are not treated as exclusive.

## Reproduction

The source-coordinate substitution and the corrected post-data are enough to
derive the continuing source-chart fields.  Let

```text
upivot = sourceChartMap(J+1,J+1) = u,
post   = pre.case2Succ(upivot).
```

The recurrence post-data are the concrete `case2Succ` data:

```text
old labels keep their level and variable,
level(S,J+1) = J,
var(S,J+1) = upivot.
```

The corrected exponent post-data update only the new label `(S,J+1)`:

```text
t'_(S,J+1) = correctedCase2PivotVector,
num'_(S,J+1) = (M(S)-J)(M^(S+1)-J),
least'_(S,J+1) = J.
```

Therefore the post exponent domain, level invariant, least-value gap, and
Case 2 recurrence gap follow from the existing finite post-data lemmas.  The
unweighted continuing product is the elementary matrix identity

```text
(D''' * C').lowerRows =
  postPivotResidualBlock * sourceFollowingFactor(S,J+1),
```

where `C' = Q^{-1} C`.  The weighted continuing payload is the already proved
source-chart lower-row handoff with the successor row-weight diagonal
explicit, plus the finite fact that the displayed source chart sends every
center generator into the ideal `(u)`.

The stopped fields in the package have not changed mathematically.  They are
still the previously accepted branch implications:

- actual-width stopped gives original terminal rows and relabelled `(S+1,0)`
  level/exponent certificates;
- row-exhausted terminal-last gives transported prefix rows, not original rows;
- row-exhausted source-suffix keeps the suffix product explicit.

The only change is that the package constructor no longer asks callers to
supply `ChartRegular`, `TransitionRegular`, or a
`Case2ResidualBlockChartFamilyBoundary`.  For the stopped terminal helper
calls still phrased through the old boundary API, the proof uses the canonical
`True`-predicate inhabitant of that abstract boundary.  This removes a
vacuous caller obligation but does not turn the stopped terminal helpers into
source-produced chart theorems.

## Proved

- A continuing product/post-data wrapper with no chart-family argument.
- A continuing weighted finite-center payload with no chart-family argument.
- A frontier implication package with no external chart-family arguments.
- The old chart-family-bearing package remains available as a compatibility
  API.

## Not Claimed

- No construction of an affine blow-up atlas.
- No chart coverage or transition regularity.
- No source production of `Csucc`, `C'^(S+1)`, or suffix data.
- No stopped-branch exclusivity.
- No original-row statement in the row-exhausted branch.
- No analytic Jacobian, normal crossings, pole order, or RLCT statement.
- No repair of the printed Case 2 vector mismatch.

## Kill Conditions

- If a stopped field starts exposing relabelled `(S+1,0)` certificates in the
  row-exhausted branch, the package is overclaiming.
- If a continuing field loses the explicit successor row-weight diagonal, it
  is conflating weighted and unweighted products.
- If the package result is later read as chart production or transition
  regularity, its name or statement must be tightened.
