# Review - A4 Case 2 displayed transition microcertificate contribution

Date: 2026-06-24.

Reviewer: xhigh scout `Hubble the 2nd`.

Verdict: pass after documentation precision fixes.

## Findings

- Low: the initial docs source-anchored the arbitrary all-pivot source chart too
  directly to Aoyagi pp. 19-22.  Aoyagi prints the displayed top-left chart;
  the all-pivot selected-entry chart family is our finite formal wrapper around
  the same elementary selected-entry algebra.  The reproduction and statement
  card have been updated to say this.
- Low: the initial statement card's assumptions paragraph was imprecise.  It
  now lists the actual theorem assumptions: `hS`, `hSL`, `hcont`, `hnext`,
  `pre`, `exponentPre`, `levelInv`, `leastValueGap`, `sourceChart`, and
  `hdisplayed`.

No Lean/math blocker was found.

## Fidelity Check

The denominator is the source-normalized displayed coordinate, and the proof
transports `hdisplayed` to the displayed target pivot by unfolding
`finsetSubtypeChartEquiv_displayedChartIndex`.

The target loss unit and target formal Jacobian/prior determinant stay target
displayed-chart data.  The source-facing statement is only the finite loss and
loss monomial identity via chart-map equality.

## Verification

Reviewer-observed commands:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/sorries
git diff --check
```

Controller also ran:

```text
lean/scripts/lb DLNFibre
```

All passed; sorry scan reported:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```
