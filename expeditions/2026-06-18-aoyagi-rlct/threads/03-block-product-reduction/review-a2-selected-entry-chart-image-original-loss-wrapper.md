# Review - A2 selected-entry chart-image original-loss wrapper

Date: 2026-06-25.

## Verdict

Accepted.

The reviewer found no mathematical fidelity issue.  The main theorem remains
scoped to the finite selected-entry chart image: the integral is restricted to

```text
U ∩ chartMap pivot '' signedBoxSet Rres.
```

The adapted-product lower bound is an explicit hypothesis on that chart image.
The proof combines only the endpoint loss comparison with the selected-entry
chart-image local-measure handoff.

## Conditional Source-Stratum Wrapper

The later source-stratum theorem in the same Lean file is also within scope:
its docstring says the source-rank stratum equality is assumed, and the
statement includes an explicit hypothesis

```text
hsourceStratum_eq :
  paperEndpointFixedBaseSourceRankStratum = chartMap pivot '' signedBoxSet Rres.
```

Thus it does not prove p.13 source coverage.

## Verification

The reviewer typechecked
`lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean`.
The controller also verified:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
scripts/sorries
git diff --check
```

The full build passed; the sorry scan reported `0 sorry, 0 #exit,
0 native_decide, 0 axiom`; and diff hygiene passed.
