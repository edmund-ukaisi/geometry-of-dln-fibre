# Reproduction - Selected-entry analytic atlas boundary

Date: 2026-06-24.

Status: pen-and-paper boundary contract for the next A4 lane.  This note
does not claim a new Lean theorem.

## Question

The finite selected-entry layer already has one-chart and all-pivot
normal-crossing certificate spines.  The A4 source-production lane is blocked
if it keeps adding `SourceProductionObligation` wrappers, because those are
inhabited by formula-level successor choices.  The next useful question is:
what exactly must be added to turn the finite selected-entry certificate into
the analytic atlas producer needed by the final A0/A6 sockets?

## Source Anchors

Aoyagi PDF pp. 5-6 gives the normal-crossing reading: after a proper analytic
map `pi`, the composed function `K(pi(u))` and the prior/Jacobian factor have
monomial normal-crossing forms with nonzero regular factors, and the
RLCT/pole order are read from the finite exponents.  The current project
treats only the normal-crossing-to-RLCT extraction as cited.

Aoyagi PDF pp. 19-22 gives the displayed Case 2 local blow-up calculation:
the selected residual-block pivot chart, the updated `b'_r =
u_{S,J+1} b_r`, regular row/column operations `P` and `Q`, the transported
following factor `C'_J^(S+1)=Q^-1 C_J^(S+1)`, the cleared `D'''_J` block, and
the displayed product identity.  It supports the local selected-entry algebra
and the formula-level transported following rows.  It does not, by itself,
produce a successor analytic atlas, chart coverage, transition regularity,
suffix production, or a global normal-crossing certificate.

## Existing Lean Feed Into A0

The A0 finite spine is

```text
AoyagiNormalCrossingChartCertificate
```

with fields:

- `numCharts`, `numCoords`;
- chart-point types and nonemptiness;
- `chartMap`;
- local coordinates `coord`;
- global loss function `loss`;
- chartwise `jacobianPrior`;
- loss and Jacobian/prior units;
- loss and Jacobian/prior exponent arrays;
- monomial identities for loss and Jacobian/prior;
- unit witnesses;
- active-coordinate nonemptiness.

For a finite nonempty center, the selected-entry certificate

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate
```

already constructs this spine with:

- one chart for each selected center generator;
- one active local coordinate per chart, the selected pivot coordinate;
- loss exponent `1`;
- Jacobian/prior exponent equal to the number of non-pivot center
  coordinates;
- finite ratio `|center|/2` in every chart;
- finite exponent minimum `|center|/2`;
- chartwise minimum count `1`;
- finite exponent order `1`;
- monomial loss identity given by the selected-entry square-sum factor
  `u^2 * (1 + sum y_i^2)`;
- formal pivot-first Jacobian determinant `u^(|center|-1)`;
- unit witnesses for the square-sum factor and the formal determinant unit.

In Case 2, the specialized certificate is

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
```

and the displayed-overlap contribution theorem

```text
sourceChartTransitionPoint_displayed_microcertificateContribution_summary_of_displayed_normalized_ne_zero
```

packages transition to the displayed chart, finite monomial loss,
formal determinant, and ratio/count/order facts for the displayed local
coordinate.

## Pen-and-paper Check of the Finite Algebra

Let the finite center have coordinates `(z_i)_{i in I}` and choose a pivot
`p in I`.  On the selected-entry chart write

```text
z_p = u,
z_i = u y_i       for i != p.
```

Then the squared center contribution is

```text
sum_i z_i^2 = u^2 * (1 + sum_{i != p} y_i^2).
```

Over an ordered field the unit factor is nonzero because
`1 + sum y_i^2 > 0`.  The pivot-first coordinate map has variables
`(u, y_i)_{i != p}` and formal Jacobian determinant

```text
u^(|I|-1).
```

Thus the A0 finite exponent data for the selected-entry center contribution
are:

```text
loss exponent k = 1,
Jacobian/prior exponent h = |I|-1,
ratio (h+1)/(2k) = |I|/2,
order contribution = 1.
```

For Case 2, `I` is the residual-block pivot set
`case2ResidualBlockPivotEntries n S J`, whose cardinality is

```text
(prefixMinNat n S - J) * (n(S+1) - J).
```

This matches the corrected Case 2 finite numerator used by the existing
Lean certificates.  This calculation is elementary and already banked in
Lean; it is not the missing step.

## Missing Analytic Atlas Fields

To turn the finite selected-entry certificate into a real A4 producer for the
final Theorem 2 socket, a future interface must add fields that are not
present in the finite spine:

1. Analytic chart domains.

   The current `ChartPoint c` is a type of formal chart points.  A real atlas
   needs domains or neighborhoods in the original parameter space and in each
   chart coordinate space.

2. Coverage.

   The finite all-pivot family proves selected-entry map coverage for the
   center variables.  A real atlas needs coverage of the relevant source
   neighborhood or exceptional divisor branch after each blow-up step.

3. Regular/analytic chart maps.

   The coordinate formulas are polynomial or rational on nonzero overlaps, but
   Lean currently records them as algebraic maps over fields.  A source
   producer must state and prove the analytic/regular property needed by the
   cited normal-crossing extraction theorem.

4. Transition regularity.

   The finite transition maps have formulas such as
   `u_target = u_source * y_target` and normalized residual quotients on
   nonzero overlaps.  The existing cocycle and inverse laws are finite
   coordinate equalities.  A real atlas needs regular transition maps on
   actual overlap domains.

5. Unit nonvanishing on neighborhoods.

   The selected-entry square-sum unit is nonzero pointwise over ordered
   fields.  The global A0 theorem needs the appropriate nonvanishing/regular
   unit statement on chart domains, and it must be preserved through the
   subsequent `P/Q`, suffix, and product transformations.

6. Analytic Jacobian/volume-form compatibility.

   Existing determinants are formal pivot-first determinants.  A full
   normal-crossing chart producer needs the analytic Jacobian or volume-form
   factor that the extraction theorem consumes.

7. Source-produced successor data.

   The finite Case 2 stack currently accepts `C`, `Ctail`, `Csucc`, or
   `Cterm` through supplied or formula-level data.  A real atlas boundary must
   say how the successor following object, terminal object, and suffix product
   are produced by the chart construction.

8. Branch and termination coverage.

   Aoyagi's prose branches between same-stage continuation and stage advance.
   The atlas producer must prove that all branch cases are covered, that the
   stopped cases use the correct actual-width or row-exhausted hypotheses, and
   that the recursive process terminates.

## Non-redundant Lean Boundary Shape

A useful Lean-facing boundary should not be another constructor for
`SourceProductionObligation`.  It should be a separate supplied or eventually
proved structure whose fields map to the final A0/A6 sockets, for example:

```text
SelectedEntryAnalyticAtlasBoundary
```

with fields for:

- an atlas-produced or explicitly supplied `AoyagiNormalCrossingChartCertificate`,
  not one inferred from the finite selected-entry certificate alone;
- a coverage statement for the relevant source neighborhood or branch;
- chart regularity;
- transition regularity;
- unit nonvanishing/regularity beyond pointwise algebra;
- analytic Jacobian/volume-form compatibility;
- source-produced successor/suffix data or an explicit handoff to the next
  recursive chart producer.

The kill condition is strict: if the structure can be inhabited by
`SelectedEntryChartFamilyBoundary.exists_trivial`,
`Case2ResidualBlockChartFamilyBoundary.exists_trivial`, or
`SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`, then
it is not the desired boundary.

## Next Work

The next formalisation-ready step is not a Lean theorem yet.  It is an
independent checker pass on this boundary and then a statement card spelling a
minimal Lean structure for the analytic atlas fields.  Only after that should
we decide whether the first Lean slice is:

- a new supplied boundary structure tying selected-entry charts to A0 chart
  certificates, or
- a concrete finite theorem that fills one of the missing fields without
  pretending to solve the analytic atlas.

## Nonclaims

- No theorem here proves analytic chart coverage.
- No theorem here proves transition regularity.
- No theorem here source-produces `Csucc`, `C'^(S+1)`, `Cterm`, or suffixes.
- No theorem here proves the analytic Jacobian/volume-form statement.
- No theorem here proves global normal crossings, termination, pole order, or
  RLCT.
