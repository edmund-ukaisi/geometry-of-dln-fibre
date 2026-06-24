# Audit - Case 2 post-constructed-Cprime source-production boundary

Date: 2026-06-24.

Status: controller boundary audit after the constructed old-top/free-`Cprime`
transition stack theorem.  No new Lean theorem is claimed in this note.

## Trigger

The latest landed A4 theorem is

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.
  sourceChartTransitionPoint_displayed_continuingSourceCurrentStack_constructedWithOldTopFromCprime_sourceSubstitution_of_displayed_normalized_ne_zero
```

It specializes the displayed-overlap source-current stack wrapper to the
constructed old-top/free-`Cprime` following factor.  The proof builds

```text
SourceProductionObligation.of_constructedWithOldTopFromCprime_terminalStack
```

from the canonical formula-level constructor

```text
SourceProductionObligation.of_formulaSuccessor_transportTerminalRows.
```

This banks the current finite stack path: the source-current block is
`[Cold; Q*Cprime]`, the successor block is the formula-level successor for
that constructed source factor, and the terminal matrix inside the obligation
is the source-row reindexing of `[Cold; top(Cprime)]`.

## Boundary Check

Aoyagi PDF pp. 19-22 supports the displayed local Case 2 calculation:
selected pivot chart, `b'_r = u_{S,J+1} b_r`, regular `Q` and `P`, the
transported factor `C'_J^(S+1) = Q^-1 C_J^(S+1)`, the cleared `D'''_J`
block, and the displayed product identity.  The existing Lean stack and
transition wrappers faithfully package these finite identities under explicit
branch hypotheses.

What remains outside the current proof boundary is not more `Q^-1*C` algebra.
The missing source-production data are:

- a source-produced successor following object, not merely the formula-level
  `case2DisplayedSourceSuccessorFollowingFactor`;
- production or inheritance of the suffix family, rather than supplied
  `Ctail` and `sourceSuffixProduct`;
- successor or terminal chart-family construction;
- chart coverage and transition regularity;
- coordinate-derived recurrence and exponent post-data where those are still
  supplied;
- analytic Jacobian/volume-form compatibility, normal crossings, termination,
  pole order, and RLCT extraction.

## Redundancy Decision

Do not pursue another constructed old-top/free-`Cprime` specialization of the
displayed `reindexedNextSourceProduct` wrapper unless a downstream theorem
directly consumes that exact statement.  It would use the same supplied-
successor product transition and the same canonical formula-level obligation
constructor already consumed by the landed source-current stack theorem.

Do not pursue another selected-entry squared-center/formal-Jacobian
microcertificate wrapper merely to expose the same transition data.  The
finite microcertificate, transition evaluation, and displayed contribution
package are already banked.

## Stricter Interface Kill Condition

A future "source-production" interface is non-redundant only if it cannot be
inhabited by

```text
SourceProductionObligation.of_formulaSuccessor_transportTerminalRows
```

plus definitional choices of `Csucc` and `Cterm`.  At minimum it must contain
some field not already formula-level, such as a produced successor chart
family, real chart coverage/transition regularity, source-produced suffix
data, or a coordinate construction of the post-state data.  If a proposed
interface can be filled by the current constructor after a `simpa`, it is an
API wrapper, not A4 source progress.

## Next Controller Direction

The A4 Case 2 lane should pause before adding more wrapper theorems.  The next
source-moving A4 task would need a pen-and-paper reproduction of exact
successor chart/source data: what the produced chart tokens are, what maps
they carry, how suffixes are produced or inherited, and which regularity and
coverage fields are proved rather than supplied.

If that cannot be extracted from Aoyagi pp. 19-22 without adding independent
atlas machinery, the better near-term move is to switch lanes to another
final-Theorem-2 obligation, especially A2 source-hypothesis/rank-stratum
handling or selected-cutpoint/Definition-3 provenance.  A5 exact terminal
order remains suspect because of the already-recorded Lemma 5 obstruction,
and A3 deepest-singular-point work remains outside the current citation
boundary unless independently reproduced.

## Claim Discipline

Any future theorem in this region must keep its name below its statement.  In
particular, do not claim source production, chart coverage, transition
regularity, global normal crossings, pole order, termination, or RLCT unless
those fields are actually present and proved.
