# Reproduction - Case 2 true-predicate next boundary

Date: 2026-06-22.

Status: Lean API hardening and source-boundary audit.  This is not
chart/source production.

## Source Anchor

Aoyagi PDF pp. 21-22, Case 2.  After the displayed transformation

```text
C'_J^(S+1) = Q^-1 C_J^(S+1)
```

and the regular `P,Q` calculation, the paper says that if the same-stage block
still continues then "we have the inductive statement with `J` increased by
one."  In the Lean refinement, the displayed pivot is valid under

```text
J+1 <= prefixMinNat n (S+1),
```

while the next residual center after increasing `J` is nonempty only under the
stronger guard

```text
J+2 <= prefixMinNat n (S+1).
```

The source sentence does not construct a successor affine atlas, source-produce
the successor following factor, produce the remaining suffix, or prove coverage
and transition regularity.  It only points to the inductive continuation.

## API Finding

The current Lean type

```text
SelectedEntryChartFamilyBoundary center ChartRegular TransitionRegular
```

is an abstract implication boundary:

```text
p in center -> ChartRegular p
p in center -> q in center -> TransitionRegular p q.
```

Therefore an existential of the form

```text
exists ChartRegular TransitionRegular,
  SelectedEntryChartFamilyBoundary center ChartRegular TransitionRegular
```

is always inhabited by choosing both predicates to be `True`.  Specializing to
Case 2 gives the same formal witness for

```text
exists ChartRegular TransitionRegular,
  Case2ResidualBlockChartFamilyBoundary n S (J+1)
    ChartRegular TransitionRegular.
```

This is a property of the current interface, not a mathematical construction
from Aoyagi's coordinates.

## Lean Targets

The slice adds:

```text
SelectedEntryChartFamilyBoundary.exists_trivial
Case2ResidualBlockChartFamilyBoundary.exists_trivial
Case2ResidualBlockChartFamilyBoundary.continuingSuccessorBoundary_exists_truePredicates
SourceProductionObligation.of_formulaSuccessor_transportTerminalRows_truePredicateNextBoundary
```

The last theorem reuses the previous canonical formula-level constructor and
fills its continuing next-boundary argument with the `True`-predicate formal
boundary.

## Interpretation

This removes the formal need to supply a next-boundary inhabitant in the
canonical formula-level obligation constructor.  It also shows that this field
was too weak to represent genuine chart production: as currently stated, it
does not carry a coordinate chart map, an atlas, transition formulas, coverage,
or any relation to the produced successor following object.

The real remaining A4 frontier is unchanged:

- source production of `Csucc` or `C'^(S+1)` as a successor object;
- production or inheritance of the source suffix;
- chart coverage and geometrically meaningful transition regularity;
- coordinate derivation of corrected post-data;
- Jacobian arithmetic, normal crossings, pole order, termination, and RLCT.

## Nonclaims

This theorem does not prove Aoyagi's inductive continuation.  It does not
construct an affine blow-up chart, prove regularity of coordinate transitions,
source-produce `C'^(S+1)`, source-produce suffix products, derive corrected
post-data, prove normal crossings, prove pole order, or compute RLCT.

## Kill Conditions

- Do not cite `exists_trivial` as chart production.
- Do not interpret `True` predicates as geometric regularity.
- Do not treat the resulting `SourceProductionObligation` as a full successor
  transition theorem.
- If downstream code needs real chart regularity, strengthen the interface
  before using this existential boundary.
