# Review - Definition 3 nonconstant `(1,2,2)` example

Reviewer: xhigh `Mencius the 3rd`.

Status: passed.

## Verdict

Formalise it as a small diagnostic/example theorem, not as a new existence
principle.

For `L=2`, `r=0`, and reduced widths `(1,2,2)`, the all-source selected sum is
`5`, and Definition 3's strict selected inequalities are:

```text
2*1 < 5,    2*2 < 5,    2*2 < 5.
```

The nonselected fields are vacuous because source positions `1,2,3` are all
selected.  The example exercises the all-source constructor and complements
the negative `(1,2,100)` guardrail.

## Required Shape

Return consecutive cutpoints, source data, the selected reduced-width family,
a ceiling datum, the concrete values `m 0 = 1`, `m 1 = 2`, `m 2 = 2`, and a
nonconstancy witness such as `m 0 != m 1`.

It is acceptable to include the standard selected reduced-width ceiling
package fields.  Do not require closed-form `ceilWidth` or `aParam`; the
existing existential package does not expose them.

## Nonclaims

This is not arbitrary source-data existence, not a classification of
Definition 3, not uniqueness for selected cutpoints or ceiling data, not a
claim that all nonconstant profiles work, and not an Eq5, chart, pole-order,
or RLCT result.
