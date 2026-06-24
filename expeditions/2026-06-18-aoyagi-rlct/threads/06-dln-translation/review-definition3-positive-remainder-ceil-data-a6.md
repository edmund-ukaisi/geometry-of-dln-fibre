# Review - Definition 3 positive-remainder ceiling data

Date: 2026-06-24.

Reviewer: xhigh independent explorer `Nietzsche the 3rd`.

## Verdict

PASS.

## Checked Source Fidelity

The reviewer checked the reproduction against Aoyagi Definition 3 on PDF
pp. 8-9.  The slice uses the `ell+1` selected widths, the defining inequality

```text
M - 1 < T / ell <= M,
```

and the residue definition

```text
a = T - (M - 1) ell.
```

The notation `T` is local to the reproduction note for the selected-width sum.

## Checked Arithmetic

The positive-remainder convention is correct, including the case `a = ell`.
If

```text
T = ell * q + a,        1 <= a <= ell,
```

then `T / ell = q + a/ell` and `0 < a/ell <= 1`, so Definition 3's ceiling
integer is `q + 1` and the residue parameter is `a`.

## Lean Scope

The reviewed target matches the existing Lean structure:
`AoyagiDefinition3CeilData` stores only the selected-sum identity and the
bound `0 < aParam <= ell`.  The new constructor should be read as finite
ceiling/residue arithmetic from a supplied positive-remainder decomposition.

The reviewer accepted the source-facing package as consistent with the
existing APIs, but the controller narrowed the implemented Lean slice to the
pure constructor to avoid wrapper churn before a downstream consumer exists.

## Nonclaims

No uniqueness theorem, selected-cutpoint existence, Definition 3
classification, Eq5 payload, Lemma 5 exactness, chart production, normal
crossings, pole order, or RLCT extraction is proved.
