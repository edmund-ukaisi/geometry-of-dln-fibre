# Review - A4 selected-entry transition inverse

Date: 2026-06-24.

Reviewer: `Plato the 2nd`, xhigh-effort independent subagent.

Status: pass.  No blocking findings.

## Scope

Reviewed the finite selected-entry normalized-coordinate transition and inverse
slice:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`;
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-selected-entry-transition-inverse-a4.md`;
- `statement-card-a4-selected-entry-transition-inverse.md`.

## Findings

No blocking findings.

The reviewer found no mathematical/formalisation mismatch.  The denominator is
consistently the normalized target coordinate `x_q`, not `u*x_q`, in the
generic normalized law, the generic inverse theorem, and the Case 2 wrapper.

The inverse theorem is correctly scoped as a chart-point identity, not equality
of raw ambient residual functions.  The proof compares residual coordinates
only through the erased source-pivot chart point, and the docs explicitly avoid
the raw-residual overclaim.

The source boundary is also explicit: this is reconstructed finite
selected-entry algebra from Aoyagi's displayed selected-pivot chart, not a
claim that Aoyagi prints every pivot chart.

## Gates

The reviewer ran and passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reports:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

The full-library build completed with pre-existing warnings outside this slice.

## Limitations

Direct PDF extraction/rendering of Aoyagi 2023 was not available in this VM.
The review therefore checked the local source-boundary notes and the Lean
formalisation rather than independently extracting pp. 20-21 from the PDF.
