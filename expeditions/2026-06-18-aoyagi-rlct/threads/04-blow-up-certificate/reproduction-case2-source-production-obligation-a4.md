# Reproduction - Case 2 Source Production Obligation

Date: 2026-06-22.

Status: Lean interface target for the branchwise successor-production
boundary.  This is not a source-production theorem.

2026-06-22 update: the `continuing_suppliedNextChartFamily` field described
below has been removed from the current Lean structure after an API audit
showed that the existential was inhabited by `True` predicates and did not
encode source production.  See
`reproduction-case2-source-production-obligation-remove-vacuous-next-boundary-a4.md`.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  The source calculation gives the displayed
selected chart at `(J+1,J+1)`, the regular matrices `Q` and `P`, and the
formula

```text
C'_J^(S+1) = Q^-1 C_J^(S+1).
```

The source then branches according to whether the same-stage process
continues or the terminal block advances to stage `S+1`.

The previous boundary note
`reproduction-case2-branchwise-successor-production-boundary-a4.md` records
the needed refinement: under the standing displayed-pivot hypotheses

```text
1 <= S,    S <= L,    J+1 <= prefixMinNat n (S+1),
```

the Lean payloads must remain branchwise.  The continuing payload uses
`J+2 <= prefixMinNat n (S+1)`.  The actual-width stopped payload uses
`n(S+1)=J+1`.  The row-exhausted stopped payload uses
`prefixMinNat n S=J+1`.  The stopped hypotheses are not treated as mutually
exclusive.

## Interface Meaning

The new Lean structure records what a later source-production theorem must
supply, while keeping current finite formulas available:

- `frontier` packages the current displayed source-chart frontier payloads.
- `Csucc_eq_formula` identifies a supplied `Csucc` with the formula-level
  `case2DisplayedSourceSuccessorFollowingFactor`.
- `continuing_frontier` supplies the weighted successor-following frontier
  payload under the stronger nonempty-next-center guard.
- `actualWidth_frontier` supplies the actual-width stopped source-suffix
  payload using the real `sourceSuffixProduct`.
- `actualWidth_Cterm_eq`, `actualWidth_level`, and `actualWidth_exponent`
  record original terminal rows and the `(S+1,0)` relabelled certificates
  only under actual-width exhaustion.
- `rowExhausted_frontier` and `rowExhausted_Cterm_eq` keep the row-exhausted
  terminal object in transported-prefix-row form.

The structure intentionally has no constructor from
`Case2DisplayedSuppliedChartFamilyBoundary`.  The current displayed chart data
proves many finite payloads, but not source production of the successor
object, suffix, or next chart family.

## Proved, Supplied, Deferred, Cited

Proved at this Lean slice:

- the type-level interface is available as a `Prop` structure;
- its fields keep the continuing, actual-width, and row-exhausted payloads
  separate;
- the row meanings in actual-width and row-exhausted branches are represented
  by different terminal-row equalities.

Supplied by an inhabitant of the interface:

- the successor following object `Csucc`;
- the terminal source matrix `Cterm`;
- the next continuing chart-family boundary;
- branch payloads under their explicit branch hypotheses;
- the source suffix factors and current source following factor.

Deferred:

- constructing an inhabitant from Aoyagi's coordinates;
- source production of full `C'^(S+1)`;
- source production or inheritance of the suffix;
- successor chart coverage and transition regularity;
- coordinate derivation of corrected post-data;
- Jacobian arithmetic, normal crossings, pole order, termination, and RLCT.

Cited:

- none at this A4 interface.  The only planned citation boundary remains the
  later normal-crossing-to-RLCT extraction.

## Kill Conditions

- Do not add an `of_...` theorem from the current displayed boundary.
- Do not use failure of `J+2 <= prefixMinNat n (S+1)` as actual-width
  exhaustion.
- Do not replace row-exhausted transported rows by original rows without
  `n(S+1)=J+1`.
- Do not relabel row-exhausted data to `(S+1,0)` unless actual width is also
  supplied.
- Do not make the stopped branches exclusive.
- Do not add Jacobian, normal-crossing, pole-order, RLCT, or quiver-paper
  content to this interface.
