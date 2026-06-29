# Reorientation - A2 Source-Measure Frontier

Date: 2026-06-29.

Status: post-interruption controller reorientation.  No new Lean theorem is
claimed here.

## Worktree State

The active expedition worktree is:

```text
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct
```

The active branch is:

```text
expedition/aoyagi-rlct
```

After `git fetch --all --prune`, the branch was clean and equal to its
upstream:

```text
HEAD = origin/expedition/aoyagi-rlct = b47560c6
```

The latest banked theorem is the Case 2 source-rank-supported endpoint-basis
original-loss finite-integral bridge.  It is only a support restatement over
`mu.restrict U`; it does not prove source-rank coverage, selected-entry
source/image equality, source-prior transport, normal crossings, pole order,
or RLCT.

## Current A2 Boundary

The local retained-passive source coverage socket is not the next hard gap.
The generic coverage inclusion used by local-measure consumers is already
discharged by:

```text
exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase
```

This theorem chooses an open neighborhood inside the retained-passive local
source preimage.  It is useful bookkeeping, but further repackaging of it would
not move the source-measure frontier.

The reduced raw-order retained-passive chart layer is also mostly closed.  The
direct determinant-chart measure and the raw-order inverse-Jacobian source
measure are connected by:

```text
measure_map_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_restrict_detChart_eq_map_rawOrderSourceChart_withDensity_inverseJacobian
```

and the Case 2 inverse-Jacobian finite-integral wrappers consume the selected
entry determinant-chart residual theorem.  In the Case 2 wrappers, the
remaining explicit measure hypothesis has the form:

```text
m.restrict Sdet = Measure.map chart weightedBox
```

where `chart` is the endpoint-transported selected-entry center-coordinate
chart and `weightedBox` is the selected-entry signed box with source density.
This is a chart-produced determinant-coordinate measure hypothesis, not an
external/original DLN source prior.

## Source Check

Aoyagi pp. 10-13 explicitly provide:

- Lemma 2 block elimination for a full-rank leading block.
- Theorem 3 product diagonalisation by iterating the block elimination.
- The p.13 product-difference display
  `[C1-Er, -F2; -F3, prod C^(s)-F3F2]`.

They do not explicitly state a measure pushforward from selected-entry signed
box coordinates to full determinant-chart Haar measure, nor an original
source-prior/Jacobian theorem.  Any such theorem must be constructed as a
retained-passive coordinate package with passive variables included.

## Next Non-Wrapper Target

The next A2 work should not add another finite-integral wrapper.  The useful
target is a pen-and-paper construction package for a retained-passive p.13
coordinate domain that includes the passive variables suppressed by the
reduced selected-entry section.

The first reproduction should decide, with formulas, which of the following is
actually provable:

1. A retained-passive chart whose source map has a local inverse and whose
   pushforward gives the determinant-chart or raw-order Haar measure with an
   explicit Jacobian density.
2. A weaker product-measure theorem for retained coordinates, with passive
   Jacobian factors shown to be local units.
3. A proof that the selected-entry chart-produced measure is intentionally
   lower-dimensional and cannot replace the full determinant-chart/raw-source
   prior without adding passive variables.

The reproduction must name the coordinate domain, source map, local inverse,
coverage or image theorem, measure pushforward, passive-unit Jacobian factors,
and residual/loss compatibility.  It must not collapse chart-produced measure,
raw Haar transport, and original source prior into one statement.

## Kill Conditions

- Do not use the current reduced selected-entry section to claim full
  determinant-chart Haar or raw-Haar pushforward.
- Do not call the raw inverse-Jacobian chart-produced measure an original DLN
  prior.
- Do not drop the explicit `m.restrict Sdet = Measure.map chart weightedBox`
  hypothesis unless a source-backed pushforward theorem is proved.
- Do not spend the next Lean tide on a wrapper that still assumes the same
  measure, coverage, or source-prior field.
- Keep the normal-crossing-to-RLCT extraction as the only cited analytic
  boundary.

## Xhigh Scout Round

Three xhigh read-only scouts reported after this reorientation.

Raw inverse-Jacobian map frontier:

- The strongest existing theorem is
  `measure_map_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_restrict_detChart_eq_map_rawOrderSourceChart_withDensity_inverseJacobian`.
  It identifies the fixed-base retained-passive determinant-chart source
  measure with the raw-order inverse-Jacobian chart measure.
- It does not identify an original/external source prior with that measure.
- The Case 2 inverse-Jacobian lane still keeps the determinant-chart
  pushforward
  `m.restrict Sdet = Measure.map chart weightedBox` explicit.

Local-source/source-rank coverage frontier:

- The local `hcoverage` used by the generic local-measure socket is already
  discharged for the retained-passive local source by choosing an open subset
  of the determinant-chart preimage.
- This is not source-rank openness and not selected-entry image coverage.
- Current support theorems show constructed Case 2 selected-entry chart points
  land in `sourceStratum` under explicit rank equations, but they do not show
  arbitrary nearby source-rank points are produced by the selected-entry chart.

Aoyagi pp. 10-13 source-fidelity frontier:

- The source explicitly supports the finite Schur/block substitutions, the
  inductive product diagonalisation, the p.13 product-difference display, and
  the regular-variable count.
- It does not state source-rank coverage, raw/source Haar pushforward,
  source-prior density transport, or selected-entry signed-box coverage of the
  determinant chart.
- These missing fields may be elementary, but they must be constructed with a
  named coordinate domain, local inverse, image/coverage theorem, measure
  theorem, and passive-unit Jacobian accounting.

Controller decision: the next artifact is a pen-and-paper retained-passive
source-prior/passive-variable construction reproduction.  It should explain
why the reduced selected-entry section cannot replace full raw Haar, then
write the larger retained-passive coordinate package needed for a genuine
measure or source-prior theorem.
