# Boundary - corrected closed-form cutoff versus printed Definition 3

Date: 2026-06-25.

Status: controller synthesis from xhigh source, Lean/API, and hardening scouts.

## Source And Formalisation Issue

Aoyagi Definition 3 on PDF pp. 8-9 prints the nonselected upper inequality
with coefficient `ell - 1`.  The existing source-data formalisation records
that printed condition in `AoyagiDefinition3SourceData`; several diagnostic
obstruction theorems intentionally depend on that printed reading.

The newer `ClosedForm.lean` layer uses a repaired binding cutoff:

```text
IsAoyagiEll M l :=
  1 <= qipA M l and (l = N or qipA M (l+1) <= 0).
```

This corresponds to replacing the inactive threshold by coefficient `ell`,
and to reading selected widths as an indexed sorted prefix.  That repaired
reading is consistent with the closed-form lambda value and with the
finite zero-run calculation, but it is not the printed `AoyagiDefinition3SourceData`
object already used in the A6 obstruction layer.

## Scout Conclusions

The source-fidelity seat judged the repaired cutoff mathematically coherent
if two choices are stated explicitly:

1. Treat the printed inactive coefficient `ell - 1` as a typo and use `ell`.
2. Count duplicate selected widths by indexed occurrence in sums.

The hardening seat rejected using `ClosedForm.lean` as Aoyagi-only proof
input in its present form because it imports Core codimension infrastructure,
uses sorted-prefix branch selection, and can be read as silently correcting
the printed Definition 3.

The Lean/API seat recommended a possible future split:

```text
PaperClosedFormArithmetic.lean
PaperClosedFormBridge.lean
```

The first would contain only repaired-cutoff finite arithmetic.  The second
would bridge that arithmetic to `FinalFormula.lean`.  Neither should import
`Core.FibreCodimFinal` or prove fibre codimension statements.

## Expedition Decision

For the Aoyagi-only expedition, `ClosedForm.lean` is currently a
Core/LR-dependent comparison bridge, not independent Aoyagi proof input.

Do not use:

```text
paperEll_unique
paperLambda_eq_lambda
codimRepCanonical_fibre_eq_two_paperLambda
```

as evidence for the printed Definition 3 or for Aoyagi's RLCT theorem.

Safe current work remains:

- source formula bookkeeping in `FinalFormula.lean`;
- supplied-source-data finite consequences in `Definition3Bridge.lean`;
- explicit diagnostics showing where printed Definition 3 branch selection is
  unsafe;
- a future repaired-cutoff module only if its statements say "corrected" or
  "repaired" and do not claim to be the printed source data.

## Kill Conditions

- Do not silently replace the printed `ell - 1` source-data field by `ell`.
- Do not claim arbitrary Definition 3 branch independence.
- Do not import `ClosedForm.lean` into Aoyagi-only theorem files.
- Do not use fibre codimension, `cValue`, `cCodim`, `kostantPartitions`, or
  `codimRepCanonical` as Aoyagi-only evidence.
- Do not identify Aoyagi's order formula with Core/LR `cTheta`.

