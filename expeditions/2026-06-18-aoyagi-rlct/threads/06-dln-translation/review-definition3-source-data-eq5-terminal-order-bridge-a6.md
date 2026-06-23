# Review - Definition 3 source-data Eq5 terminal-order bridge

Date: 2026-06-23.

Reviewer: Turing, xhigh-effort subagent.  Controller follow-up after focused
build.

## Verdict

Pass as a source-facing supplied-boundary bridge.

## Source-Fidelity Check

The wrappers keep the generated `m,data` tied to Definition 3 source data.
The Eq5 callback is indexed by the `data` produced from
`Ssrc.exists_selectedReducedWidthCeilData_of_rankWidth` and receives the
equality

```text
m = aoyagiSelectedReducedWidths H r C.
```

Thus the theorem does not assume a fixed external Eq5 payload for unrelated
ceiling data, and it does not assert uniqueness of the ceiling datum.

Cutpoint drift is explicitly blocked.  The Eq5 payload must provide

```text
P.cut = C.
```

The proof rewrites the selected-width provenance from `C` to `P.cut` before
calling the existing supplied Eq5 bridge, then rewrites the resulting final
boundary back to `C`.

## Lean/API Check

The new names are:

```text
AoyagiDefinition3SourceData
  .exists_theorem2SuppliedFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload

AoyagiDefinition3SourceData
  .exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
```

The focused module build passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.Theorem2Eq5TerminalOrderBridge
```

The result remains a supplied final boundary or supplied chart-final boundary,
not an RLCT theorem.

## Nonclaims

- No selected-cutpoint construction.
- No rank-width theorem from matrix data.
- No Eq5 endpoint-family construction.
- No source-backed Lemma 5 exactness.
- No active-ratio lower-bound theorem.
- No displayed-ratio chart-count theorem.
- No chart production, coverage, or transition regularity.
- No pole order without the explicit A0 extraction hypothesis.
- No RLCT extraction theorem.

## Residual Risk

The Eq5 endpoint payload remains a large supplied hypothesis bundle.  This
review does not certify source construction of Eq5 families, Lemma 5
exactness, active-ratio bounds, chart counts, chart production, or A0
extraction.
