# Review - Definition 3 Eq5 hsource bridge

Date: 2026-06-24.

Reviewer: Copernicus the 2nd, xhigh read-only API scout.
Post-Lean reviewer: Tesla the 2nd, xhigh read-only slice review.

Verdict: PASS for a tiny source inequality extractor and one Eq5 terminal-order
consumer.

## Findings

The Eq5 terminal-order APIs still ask explicitly for the strict selected-width
inequality `hsource`.  This is already stored in
`AoyagiDefinition3SourceData`, and after rewriting by
`m = aoyagiSelectedReducedWidths H r C` it has exactly the needed shape.

The target is source-moving because it removes a duplicated supplied source
inequality.  It is not a proof of Eq5 family construction, actual-width
dominance, or Lemma 5 exactness.

## Required Checks

- Reproduce that `selected_strict` has the exact Eq5 `hsource` shape after
  rewriting by `hm`.
- Keep the blockwise actual-width hypothesis `hactual` explicit.
- Call the existing Eq5 cardinal-squeeze theorem rather than duplicating its
  proof.

## Nonclaims

No selected-cutpoint construction, no Definition 3 source-data existence, no
Eq5 endpoint-family construction, no position-level off-selected dominance
from Definition 3, no Lemma 5 exactness/no-extra coverage, no chart production,
no normal crossings, no pole order, and no RLCT.

## Post-Lean Check

Tesla the 2nd found no issues.  The review confirmed that the bridge only
rewrites `AoyagiDefinition3SourceData.selected_strict` along
`hm : m = aoyagiSelectedReducedWidths H r C`, leaves `hactual`, block
assumptions, Eq5 construction/payload data, injectivity, and family equality
explicit, and does not overclaim charts, exactness, pole order, or RLCT.

Controller focused build passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalOrderDefinition3Bridge
```
