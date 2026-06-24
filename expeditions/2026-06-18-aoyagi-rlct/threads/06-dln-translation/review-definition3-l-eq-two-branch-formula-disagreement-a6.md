# Review - Definition 3 `L=2` branch formula disagreement

Date: 2026-06-24.

Reviewers: xhigh scout `Pascal the 3rd`; xhigh reviewer `Carver the 3rd`.

## Verdict

PASS.  No required corrections.

## Checked Source Fidelity

The review checked Aoyagi Definition 3 and Theorem 2 on PDF pp. 8-9.  Definition
3 is value-level in the selected set: a source position whose reduced-width
value equals a selected value is not treated as nonselected.  No visible
tie-breaking or branch-selection convention appears in the rendered local PDF
pages.

For the concrete profile `(2,3,3)`, the `ell=1` selected value set `{2,3}`
covers all source-range values, and the all-source `ell=2` triangle branch
also satisfies the three strict inequalities.

## Checked Arithmetic

Repeated branch:

```text
lambda = 2*3/2 = 3.
```

All-source even triangle branch:

```text
T = 8,  a = 2,  pair sum = 2*3 + 2*3 + 3*3 = 21,
lambda = -4^2/2 + 21/2 = 5/2.
```

Both finite order formulas are `1`.

## Checked Lean Scope

The Lean theorem constructs both source-data packages for the same concrete
`H`, pins both selected-width families to `aoyagiSelectedReducedWidths`, proves
the two finite lambda equalities, proves both order equalities, and proves the
finite formula values differ.

The docstring and reproduction correctly keep the result diagnostic.  They do
not claim RLCT ambiguity, chart production, normal crossings, pole order, or
extraction.

## Scout Note

The independent scout also checked the more general overlap arithmetic.  For a
profile `(y,x,x)` satisfying the all-source triangle inequalities, the
repeated branch gives `R + xy/2`; the all-source branch differs by
`(1-y^2)/8` in odd `y` and by `-y^2/8` in even `y`.  Thus a general agreement
theorem would be false, and even the odd `y=1` lambda agreement has different
finite order.
