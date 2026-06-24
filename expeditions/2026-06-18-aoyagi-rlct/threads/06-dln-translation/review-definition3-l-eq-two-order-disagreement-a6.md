# Review - Definition 3 `L=2` branch order disagreement

Date: 2026-06-24.

Reviewer: xhigh scout `Tesla the 3rd`.

## Verdict

PASS.  No required corrections.

## Checked Source Fidelity

The review checked that the theorem uses the currently formalised value-level
selected set from Aoyagi Definition 3.  The `ell=1` branch is valid because the
selected value set `{1,2}` covers the third source value `2`, so no
nonselected clause applies to that source position.

The result remains finite Theorem 2 formula bookkeeping only; it does not
claim analytic RLCT or pole-order ambiguity.

## Checked Arithmetic

Repeated branch:

```text
ceilWidth = 1+2 = 3,
a = 1,
pair sum = 1*2 = 2,
lambda = 1,
order = 1*(1-1)+1 = 1.
```

All-source odd triangle branch:

```text
T = 5 = 2*2+1,
ceilWidth = 3,
a = 1,
pair sum = 1*2 + 1*2 + 2*2 = 8,
lambda = 1,
order = 1*(2-1)+1 = 2.
```

Thus the two branch choices have equal finite lambda formula values but
different finite order formula values.

## Checked Lean Scope

The Lean theorem constructs both source-data packages for the same concrete
`H`, pins both selected-width families to `aoyagiSelectedReducedWidths`, proves
both finite lambda equalities, proves the two finite order equalities, and
proves the order formulas differ.

## Value

This complements the `(2,3,3)` diagnostic: `(2,3,3)` shows finite lambda
disagreement with equal order, while `(1,2,2)` shows equal finite lambda with
order disagreement.  Together they rule out treating branch overlap as harmless
for either part of Theorem 2's finite payload.
