# Reproduction - A6 Definition 3 `L=2` branch-disjunction formula

Date: 2026-06-26.

Status: pen-and-paper reproduction before Lean implementation.

## Source Anchor

Aoyagi Definition 3 and Theorem 2, PDF pp. 8-9, compute the finite formula
from a chosen Definition 3 branch.  The source audit
`source-audit-definition3-branch-selection-a6.md` records that pp. 8-9 do not
give a canonical tie-breaker between valid branches.  Therefore the correct
finite `L=2` combined statement is a branch disjunction, not a single
branch-independent formula.

## Inputs

For `L=2`, write the three source-range reduced widths as natural numbers:

```text
M^(1)=w1,  M^(2)=w2,  M^(3)=w3.
```

Assume only that some Definition 3 source data exists:

```text
exists ell C, AoyagiDefinition3SourceData 2 ell H r C.
```

The existing classification theorem says that this is equivalent to either:

1. all three widths are positive and at least two are equal; or
2. the three all-source triangle inequalities hold:

```text
2*w1 < w1+w2+w3,
2*w2 < w1+w2+w3,
2*w3 < w1+w2+w3.
```

The classification is stated in integer reduced widths.  The natural-width
identities rewrite those integer statements to the displayed natural
statements.

## Branches

In the repeated-positive case, use the no-`hr` wrapper

```text
exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated
```

to produce an `ell=1` finite Theorem 2 package.  The branch tag records
positivity and the repeated-equality disjunction.  It does not claim a
canonical selected pair.

In the triangle case, split on the parity of

```text
T = w1+w2+w3.
```

If `T % 2 = 1`, use

```text
exists_consecutive_three_widths_theorem2Formula_of_triangle_odd
```

to produce the all-source odd branch.  If `T % 2 = 0`, use

```text
exists_consecutive_three_widths_theorem2Formula_of_triangle_even
```

to produce the all-source even branch.  Each branch keeps the triangle
inequalities and parity as explicit tags.

## Lean Shape

Add in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.exists_L_eq_two_theorem2Formula_branchDisjunction_of_sourceData
```

The conclusion is:

```text
repeated-positive formula package
or
triangle odd formula package
or
triangle even formula package.
```

Each disjunct inlines the corresponding existing formula theorem's conclusion
and carries the branch hypotheses used to produce it.

## Boundary

This is finite Definition 3/Theorem 2 branch dispatch only.  It does not select
a canonical branch, prove branch independence, identify a unique lambda/order
from arbitrary source data, add a final socket, construct Eq5 payloads or
charts, prove normal crossings, identify pole order, or extract RLCT.
