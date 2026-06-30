# Reproduction - A4 combined recurrence branch progress

Date: 2026-06-30.

Status: controller pen-and-paper reproduction before Lean.

## Question

How can the two already separated progress lanes be measured by one
well-founded branch relation?

Case 1(2) and Case 2 usually advance from `(S,J)` to `(S,J+1)` and strictly
grow the finite introduced-label support.  Stage handoff advances from `S` to
`S+1`; its support is monotone and may be unchanged at an exhausted actual
width.  Case 1(1) stays over `(S,J)` and strictly decreases the number of
introduced old labels whose recurrence level remains above `J`.

These are not the same measure, but they fit a three-coordinate descent.

## Finite Coordinates

For a recurrence-aware branch state `(S,J,level,var)`, define

```text
support(S,J) = introducedLabelFinset L n S J,

remaining(S,J)
  = #(actualWidthLabelFinset L n) - #support(S,J),

above(S,J,level)
  = #{p in support(S,J) | J < level(p)}.

stageBudget(S) = L+1-S.
```

The `above` coordinate is always bounded by `#(actualWidthLabelFinset L n)`,
since it is a filtered subset of introduced labels and introduced labels are
actual-width labels.  The stage budget is bounded by `L+1` because branch
states carry `1 <= S`.

Set

```text
Bstage = L+2,
Babove = #(actualWidthLabelFinset L n) + 1,

measure = (remaining * Bstage + stageBudget) * Babove + above.
```

This packages the lexicographic order `(remaining, stageBudget, above)` as a
single natural number because `stageBudget < Bstage` and `above < Babove`.

## Case 1(2) and Case 2

For same-stage support growth `(S,J) -> (S,J+1)`, the old progress kernel
proves

```text
support(S,J) subset_strict support(S,J+1).
```

Therefore `remaining` strictly decreases.  Since `above < B`, a one-step
decrease in `remaining` dominates any possible value of the child `above`
coordinate:

```text
child.remaining < parent.remaining
  implies
child.measure < parent.measure.
```

This applies to the displayed Case 2 continuation and to the displayed Case
1(2) row-strip payload through their existing actual-width proof for the fresh
label `(S,J+1)`.

## Stage Handoff

For a stage handoff `(S,J) -> (S+1,0)`, the finite introduced-label domain is
monotone:

```text
support(S,J) subset support(S+1,0).
```

Therefore `remaining` weakly decreases.  The stage budget strictly decreases:

```text
L+1-(S+1) < L+1-S.
```

Thus the combined weighted measure strictly decreases whether or not the
support actually grows.

## Case 1(1)

For same-domain selected-old lowering, the introduced-label support is
unchanged and `S` is unchanged, so `remaining` and `stageBudget` are unchanged.
The previous Case 1(1) plateau slice proves that supplied selected-old
level-move data erases `(s0,k0)` from the above-pivot set:

```text
above(post) = above(pre) \ {(s0,k0)}.
```

Thus

```text
post.above < pre.above
```

and the weighted measure decreases with the first coordinate fixed.

## Nonclaims

This combined progress relation is still bookkeeping.  It does not construct
source-production payloads, infer branch guards, prove that every Aoyagi branch
is produced by a chart, prove terminal coverage, full branch termination of the
analytic atlas, normal crossings, pole order, or RLCT.
