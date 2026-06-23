# Reproduction - Case 2 Branchwise Successor Production Boundary

Date: 2026-06-22.

Status: reproduction-first boundary contract.  No new Lean theorem is claimed
in this slice.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  The paper blows up the displayed residual
block at `(J+1,J+1)`, writes the selected chart with pivot variable
`u_{S,J+1}`, introduces the updated weights `b'_r = u_{S,J+1} b_r` for
`r=J+1,...,M(S)`, defines regular matrices `Q` and `P`, sets

```text
C'_J^(S+1) = Q^-1 C_J^(S+1),
```

and obtains the displayed equality

```text
P diag(b'_(J+1),...,b'_M(S)) D''_J C'_J^(S+1)
  =
diag(b'_(J+1),...,b'_M(S)) D'''_J C'_J^(S+1).
```

The paper then branches: if the next same-stage diagonal entry still exists,
the inductive statement continues with `J` increased by one; if it does not,
then `D'''_J` is a one-row or one-column terminal block and the statement is
advanced to stage `S+1`.

The Lean/A4 contract below is a refinement of that printed sentence under the
standing displayed-pivot hypotheses used by the existing Case 2 chart:

```text
1 <= S,    S <= L,    J+1 <= prefixMinNat n (S+1).
```

The last inequality is the pivot-validity condition for the displayed chart.
The continuing payload below uses the stronger condition
`J+2 <= prefixMinNat n (S+1)` because it needs a nonempty next residual
center.  This is stronger than Aoyagi's printed non-strict continuation guard.

## Common Finite Calculation

In the selected chart, `Q^-1` changes only the pivot row of the following
factor.  In source-row notation this gives a formula-level successor following
function:

```text
Csucc(r,-) =
  C(r,-)                              for r != J+1,
  top row of Q^-1 C_J^(S+1)           for r = J+1.
```

The top row is the elementary row operation

```text
(Q^-1 C)_J+1,a =
  C_J+1,a + sum_{r=J+2}^{M^(S+1)} d'_(J+1,r) C_r,a.
```

Lean already records this as the formula-level object
`case2DisplayedSourceSuccessorFollowingFactor`, with top-row, old-row, and
post-pivot-tail lemmas.  The source-current row equivalence identifies the
single interval `1..n(S+1)` with old top rows, the pivot row, and post-pivot
rows.  Under that equivalence:

```text
C                  -> [oldTop; displayedSourceFollowingFactor],
Csucc              -> [oldTop; paperCprime].
```

The landed stack theorem proves the corresponding continuing matrix identity
after right multiplication by the raw source suffix.  This is finite row and
block bookkeeping.  It does not prove that `Csucc` is chart-produced as the
next inductive source object.

## Branchwise Contract

### Continuing branch

Standing hypotheses:

```text
1 <= S,    S <= L,    J+1 <= prefixMinNat n (S+1).
```

Additional branch hypothesis for the nonempty-next-center continuing payload:

```text
J+2 <= prefixMinNat n (S+1).
```

Existing proved data:

- next residual center nonempty;
- the weighted lower-row `D'''_J C'_J^(S+1)` product in next same-stage
  source-following notation;
- the old-top/source-suffix stack identity in source-current coordinates;
- finite center principalization for the displayed current center;
- corrected post exponent, level, least-value-gap, and Case 2 gap fields,
  carried through the existing supplied-boundary theorem.

Still required for a genuine source-production theorem:

- construction of a successor chart-family boundary at `(S,J+1)`;
- proof that the formula-level `Csucc` is the source-produced next following
  object in that successor chart, not merely a row formula;
- production or inheritance contract for the remaining suffix factors;
- chart regularity, transition regularity, and coverage;
- a coordinate derivation of the corrected post-data, or an explicit statement
  that those data remain supplied.

### Actual-width stopped branch

Standing hypotheses:

```text
1 <= S,    S <= L,    J+1 <= prefixMinNat n (S+1).
```

Additional stopped-side hypothesis:

```text
n(S+1) = J+1.
```

Then the post-pivot column set in the top-row formula is empty, so the top row
of `Q^-1 C_J^(S+1)` is the original row `C(J+1,-)`.  The terminal matrix may
therefore be written using original rows `1,...,J+1`.

Existing proved data:

- original-row terminal `C'` bridge under actual-width exhaustion;
- actual-width terminal product boundary with a supplied following matrix;
- relabelled `(S+1,0)` level and exponent certificates in the existing
  actual-width package;
- finite current-center principalization.

Still required:

- source production of the terminal following product from chart data;
- chart coverage and transition regularity for the advanced stage;
- proof that supplied following factors are the actual remaining layer
  product rather than an arbitrary supplied matrix.

### Row-exhausted stopped branch

Standing hypotheses:

```text
1 <= S,    S <= L,    J+1 <= prefixMinNat n (S+1).
```

Additional stopped-side hypothesis:

```text
prefixMinNat n S = J+1.
```

Here the terminal prefix has rows `1,...,prefixMinNat n (S+1)=J+1`, but the
actual next width `n(S+1)` can be larger than `J+1`.  In that wide-next
subcase, the top row of `Q^-1 C_J^(S+1)` contains the correction sum above and
is not the original source row.

Existing proved data:

- transported terminal prefix rows;
- the same prefix rows written as original rows of the formula-level successor
  following factor;
- source-suffix terminal boundary keeping `sourceSuffixProduct` explicit;
- finite current-center principalization.

Still required:

- chart/source production of the transported terminal prefix object;
- source production or inheritance of the suffix;
- any stage-advance chart regularity and coverage;
- a separate actual-width hypothesis before replacing the transported pivot
  row by the original row.

The actual-width stopped and row-exhausted stopped hypotheses are not asserted
to be mutually exclusive.  They expose different existing Lean payloads and
may overlap in small boundary cases.

## 2026-06-23 Branch Re-Audit

Three independent xhigh scouts rechecked the continuing, actual-width stopped,
and row-exhausted stopped branches against Aoyagi PDF pp. 19-22 and the
current Lean boundary.  The durable audit is saved at
`audit-case2-branchwise-successor-production-recheck-a4.md`.

All three reached the same conclusion: the source supports only the displayed
local `Q/P` algebra, formula-level transported following rows, and finite
supplied-boundary consumers.  It does not justify a theorem that the displayed
Case 2 chart source-produces a successor following object, terminal following
object, suffix, successor chart family, chart coverage, transition regularity,
coordinate-derived corrected post-data, Jacobian data, normal crossings, pole
order, termination, or RLCT.

The re-audit also fixes the branch interpretation:

- continuing branch: keep the stronger `J+2 <= prefixMinNat n (S+1)` guard;
- actual-width stopped branch: original terminal rows are safe because the
  `Q^-1 C` correction sum is empty;
- row-exhausted stopped branch: in the wide-next subcase the pivot row is
  transported, and becomes an original row only as a row of the formula-level
  successor factor `Csucc`.

## Proved, Supplied, Deferred, Cited

Proved at the finite A4 layer:

- the displayed `Q/P` block algebra;
- the `Q^-1 C` top-row and tail formulas;
- lower-row and source-current stack presentations;
- actual-width original-row collapse;
- row-exhausted transported-prefix presentations;
- current center principalization for the selected chart.

Supplied at the current boundary:

- the chart-family boundary and regularity predicates;
- corrected post exponent/level/gap data as already isolated in Lean;
- the source following factor `C` and raw source suffix factors;
- arbitrary following matrices in several terminal wrappers;
- terminal bridge row equations unless the explicit formula-level transported
  or actual-width constructors are used.

Deferred:

- source production of the full successor object `C'^(S+1)`;
- successor chart-family construction, coverage, and transition regularity;
- source production of the suffix and remaining following products;
- coordinate derivation of corrected post-data;
- Jacobian arithmetic, normal crossings, pole order, termination, and RLCT.

Cited:

- none for this A4 boundary.  The only standing citation boundary remains the
  later normal-crossing-to-RLCT extraction.

## Kill Conditions

- Do not identify a lower tail or a source-current row formula with full
  source production of `C'^(S+1)`.
- Do not treat `SuppliedTerminalCprimeBridge` as chart production.
- Do not replace a transported row by an original row in the row-exhausted
  wide-next branch.
- Do not use failed next-continuation as a substitute for actual-width
  exhaustion.
- Do not drop the standing displayed-pivot hypotheses when using a stopped
  branch payload.
- Do not read chart coverage, transition invariance, Jacobian data, normal
  crossings, pole order, termination, or RLCT out of the Case 2 prose.
- Do not use the quiver/Lehalleur-Rimanyi paper as evidence for this Aoyagi
  boundary.
