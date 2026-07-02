# Review - A2 with-following source-density composition and contract

Date: 2026-07-02.

Reviewer: Sartre the 2nd, xhigh read-only sidecar audit.

Verdict: PASS.

## Findings

No blocking issue was found.

The `withDensity` orientation is correct.  The flattened source density is

```text
selectedEntryDensity z * rawDensity z,
```

matching Mathlib's `withDensity_mul_0` orientation.  The restricted statement
uses the same density after `restrict_withDensity`.

The contract constructor keeps the necessary hypotheses explicit:

```text
chartPiece subset sourceChart '' V
chartPiece subset p13SourceSet
Measure.map rawMap (thetaReference.restrict V) = rawHaar.restrict rawSourceSet
```

The contract stores the local source-image subset rather than replacing it by
the p.13 source-set hypothesis.

The reproduction and statement card preserve the nonclaim boundary: no raw
Haar transport, determinant-chart Haar transport, source-image coverage,
source-prior transport, normal crossings, pole order, or RLCT extraction.

## Verification

The reviewer replayed focused `lake env lean` checks for both touched Lean
modules.  The controller also replayed focused module builds, no-sorry audit,
whitespace check, and direct axiom probes for the four new declarations.
