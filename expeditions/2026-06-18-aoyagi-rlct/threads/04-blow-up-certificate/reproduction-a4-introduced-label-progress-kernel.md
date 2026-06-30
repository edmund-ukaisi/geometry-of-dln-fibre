# Reproduction - A4 introduced-label progress kernel

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before review.

## Question

Can we prove a non-vacuous termination kernel for the blow-up bookkeeping
without pretending that branch source production has already been constructed?

Answer: yes.  Use the finite set of actual source labels and measure progress
by how many labels have not yet been introduced.  A branch step that strictly
grows the introduced-label support must terminate, because there are only
finitely many actual source labels.

## Finite Supports

For layer data `L` and widths `n`, the finite actual source-label support is:

```text
actualWidthLabelFinset L n
```

A branch state records a stage/index pair `(S,J)` with `1 <= S <= L`.  Its
introduced-label support is:

```text
introducedLabelFinset L n S J.
```

Every introduced label is an actual source label:

```text
introducedLabelFinset L n S J ⊆ actualWidthLabelFinset L n.
```

Define the remaining-label measure:

```text
remaining(S,J) =
  #(actualWidthLabelFinset L n) - #(introducedLabelFinset L n S J).
```

If a child state has strictly larger introduced-label support than its parent,
then the child has strictly smaller `remaining`.  This gives a well-founded
progress relation.

## Case 2 Same-Stage Increment

For a Case 2 same-stage pivot advance from `(S,J)` to `(S,J+1)`, assume:

```text
1 <= S,  S <= L,  J+1 <= n(S+1).
```

The old support is included in the new support by monotonicity in `J`:

```text
introducedLabelFinset L n S J ⊆
introducedLabelFinset L n S (J+1).
```

The new label `(S,J+1)` witnesses strictness:

```text
(S,J+1) ∉ introducedLabelFinset L n S J
(S,J+1) ∈ introducedLabelFinset L n S (J+1).
```

Therefore the same-stage pivot advance is a progress step.  Under Aoyagi's
Case 2 displayed continuation bound

```text
J+1 <= prefixMinNat n (S+1),
```

the actual-width bound follows from `prefixMinNat_le_width`, so the same
progress step applies.

## Source Fidelity

This is finite bookkeeping around Aoyagi's statement that the Case 2 continuing
branch increases `J` by one.  It is not a source-production theorem.  It does
not prove that every Case 1/Case 2 branch has been connected to this progress
relation, and it does not fill the selected-entry analytic atlas producer's
branch-termination field.

## Kill Conditions

- An introduced label is not an actual source label.
- The new Case 2 label `(S,J+1)` is already introduced before the increment.
- The Case 2 continuation bound does not imply the actual-width label bound.
- A future branch-production theorem cannot show that its branch transitions
  strictly grow the introduced-label support.
