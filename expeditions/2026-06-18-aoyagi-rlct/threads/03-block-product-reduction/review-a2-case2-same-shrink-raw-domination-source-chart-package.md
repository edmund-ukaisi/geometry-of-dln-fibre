# Review - A2 Case 2 same-shrink raw domination and source chart package

Date: 2026-07-01.

Status: xhigh read-only review PASS.

## Checks

- The theorem returns a single final shrink `V`.
- Source-chart readback, injectivity, continuity, image measurability, and
  p.13 image inclusion are all stated for this same `V`.
- The one-stage raw composite and two-stage raw-order pushforward identities
  are stated for every source measure restricted to this same `V`.
- The reverse raw-source domination is also stated on this same `V`, under
  explicit determinant-side reverse domination, `Cdet < infinity`, a
  `baseJ.restrict V`-a.e. lower bound for `sourceDensity`, and nonzero finite
  `epsilon`.
- The proof's shrink order is the intended one: source-chart shrink `Vsrc`,
  two-stage shrink `Vtwo subset Vsrc`, then raw-domination shrink
  `V subset Vtwo`.
- The two-stage identity is transferred to `V` by applying the `Vtwo`
  identity to `sourceMeasure.restrict V`; since `V subset Vtwo`, this measure
  is unchanged by an additional restriction to `Vtwo`.

## Boundary

The theorem and reproduction note do not claim source coverage, source-rank
coverage, determinant-chart Haar transport, exact raw-Haar pushforward,
raw-Haar normalization, normal crossings, pole order, or RLCT extraction.
The determinant-side reverse domination and source-density lower bound remain
explicit hypotheses.

## Verification

Reviewer `Bohr` reran focused Lean elaboration for
`RetainedPassiveCase2PassiveThetaRawImageHandoff.lean` from the `lean/`
project root.  No files were edited.
