# Statement card - A4 selected-entry analytic atlas/source-production frontier

Status: pen-and-paper frontier specification; no Lean theorem proposed.

Reproduction:
`reproduction-selected-entry-analytic-atlas-source-production-frontier-a4.md`.

Independent review:
`review-selected-entry-analytic-atlas-source-production-frontier-a4.md`.

## Target

Record the current A4 frontier after rechecking Aoyagi pp. 19-22: the source
supports the displayed local Case 2 finite algebra, but it does not support a
constructor from finite selected-entry certificates into
`SelectedEntryAnalyticAtlasBoundary`.

## Source-Supported Content

Aoyagi pp. 19-22 support:

- the displayed Case 2 pivot chart for the residual block;
- the substitution `D_J = u D'_J` on that pivot chart;
- the weight convention `b'_i = u b_i`;
- regular elementary matrices `Q` and `P`;
- the transported following factor `C'_J^(S+1) = Q^-1 C_J^(S+1)`;
- the cleared block `D'''_J`;
- the displayed product identity after the `Q/P` operations;
- the prose instruction to continue with `J` increased or stop and advance
  `S`;
- the final candidate exponent formula.

## Source-Unsupported Content

The same pages do not define:

- analytic chart domains or source-neighborhood domains;
- chart tokens for a global atlas;
- analytic chart maps on those domains;
- coverage of the relevant source neighborhood;
- analytic or regular overlap maps;
- analytic Jacobian or volume-form factors;
- chart-produced successor, terminal, or suffix data;
- a termination proof for the full recursion as an atlas.

## Branch Separation

Any future producer must distinguish:

```text
continuing:
  J+2 <= prefixMinNat n (S+1)

actual-width stopped:
  n (S+1) = J+1

row-exhausted stopped:
  prefixMinNat n S = J+1
```

These are not interchangeable Lean-side payloads even if the source prose
groups the stopped cases as "no next same-stage pivot remains".

## Prohibited Target

Do not introduce a constructor of the following kind:

```text
SelectedEntryAnalyticAtlasBoundary.of_case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate_finiteSuppliedBranch
```

if it fills `coverage`, `transition_regular`, `source_production`, or the
other analytic fields using finite selected-entry coverage,
`SelectedEntryFiniteAffineTransitionRegularFamily`, or
`SourceProductionObligation` constructors.  That would overstate finite
selected-entry algebra as analytic atlas data.

## Required Future Fields

A non-redundant A4 producer needs fields for:

- chart domains/tokens;
- full chart maps;
- source-neighborhood coverage;
- regular overlap maps;
- unit/Jacobian/volume-form compatibility;
- produced successor/suffix/terminal data;
- branch and termination coverage.

Only a structure or theorem with fields of this kind should feed the supplied
`SelectedEntryAnalyticAtlasBoundary` sockets.

## Lean Status

No Lean file changes are expected for this card.  The existing supplied
boundary

```text
SelectedEntryAnalyticAtlasBoundary
```

remains the correct socket.  Its fields should stay supplied until a genuine
analytic atlas/source-production producer exists.

## Nonclaims

No analytic atlas existence, source production, transition regularity,
analytic Jacobian theorem, normal crossings, pole order, or RLCT follows from
this card.
