# Review - A2 Retained-Passive Nonredundant Coordinate Data

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Locke the 3rd`.

Verdict: survived.

## Target

Lean and docs for:

```text
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeMatrix_readbacks_eq_targets
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeMatrix_ext
```

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
reproduction-a2-retained-passive-nonredundant-coordinate-data.md
statement-card-a2-retained-passive-nonredundant-coordinate-data.md
```

## Checks

The reviewer found that `RetainedPassiveNonredundantCoordinateData` stores
exactly the non-dummy finite retained-passive fields: passive `A1` indexed by
`Fin M`, nonterminal `F2` indexed by `Fin (M+1)`, passive `A3` indexed by
`Fin M` with row type `κ' p.castSucc.succ`, all residual `C`, `Ctop`, and
`F3`.  For `M=0`, the passive `A1` and `A3` families are empty, as intended.

The embedding into `RetainedPassiveCoordinateData` was checked: `A1seed` uses
`Fin.cases 0 data.A1passive`, `F2full` uses `Fin.snoc data.F2 0`, and
`A3seed` uses `Fin.snoc data.A3passive 0`.  Thus the old dummy seed slots and
terminal constrained `F2` slot are filled canonically.

The reviewer checked that `toCoordinateData_passiveA1_units` correctly splits
`Fin (M+1)` into zero and successor cases, excludes zero, and applies the
passive unit hypothesis to successor indices.

The readback theorem recovers the stored fields and no dummy slots: passive
`A1`, stored `F2`, passive `A3`, `C`, `Ctop`, and `F3`.  The source-left
`F2_0` readback is a duplicate readback of an already stored `F2` coordinate,
not an additional coordinate.

The extensionality theorem legitimately reduces to
`RetainedPassiveCoordinateData.edgeMatrix_recoverable_ext` and projects the
recoverable equalities back to the nonredundant fields, yielding full equality
of the new records under the unit side conditions on both records.

The reproduction and statement card keep the nonclaim boundary: no topology,
coverage, measure/Jacobian theorem, source/image equality, normal crossings,
pole order, or RLCT is asserted.

## Verification

The reviewer ran the focused Lean check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

It completed successfully.
