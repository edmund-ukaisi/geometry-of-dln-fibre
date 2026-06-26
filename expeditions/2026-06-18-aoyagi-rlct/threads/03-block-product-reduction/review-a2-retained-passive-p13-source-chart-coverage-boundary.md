# Review - A2 Retained-Passive p.13 Source-Chart Coverage Boundary

Date: 2026-06-26.

Reviewer: Boyle the 3rd, xhigh.

Verdict: pass.  No blocking issue was found in the reproduction note,
statement card, or ledger updates.

## Findings

The proposed coverage target is only meaningful with the repair already
recorded in the card: the local source cannot be chosen as an arbitrary copy
of the source-rank stratum.  It should be tied to the retained-passive chart,
for example

```text
retainedPassiveP13LocalSource =
  {x | fixedBaseEdgeMatrix x in sourceRecursiveDetChartSet}.
```

The intended theorem should then prove a local inclusion of the source-rank
stratum into this chart-tied source:

```text
exists Ulocal, IsOpen Ulocal /\ x0 in Ulocal /\
  Ulocal inter sourceStratum subset
    Ulocal inter retainedPassiveP13LocalSource.
```

The coordinate list is sound against the Lean retained-passive data.  In
particular, `F2` is stored as the nonterminal family, `F2full` appends the
terminal zero, and the endpoint variables `A1_0` and `A3_last` are solved.
Retaining passive `F2_p` for `p > 0` is correct; fixing those variables would
define another section rather than the full retained-passive chart.

The p.13 loss/readout boundary is precise.  The displayed active block

```text
[ Ctop - I      -F2
  -F3        D - F3 F2 ]
```

uses active variables only.  Passive variables reconstruct the source edge
family and supply determinant-unit data; they are not hidden singular
variables in this readout.

The symbolic Jacobian discussion is correctly framed as boundary work, not a
Lean theorem.  A real density result still needs a local diffeomorphism,
source-measure identification, pushforward density calculation, and bounded
transported-prior statement.

The ledgers do not overclaim.  They state that no Lean theorem, coverage
removal, raw measure pushforward, Jacobian/density theorem, normal-crossing
construction, pole-order theorem, or RLCT extraction has been proved by this
boundary card.

## Residual Risk

Before formalising the next theorem, resolve the local index convention
explicitly.  The reproduction note uses the paper-side notation `N = M + 2`,
while the retained-passive Lean API uses `kappa' : Fin (M + 2)` with an edge
family indexed by `Fin (M + 1)`.

Before promoting the symbolic Jacobian calculation, define the exponent width
as the actual column width of the `A2/F2` block rather than relying on a
paper-side placeholder.
