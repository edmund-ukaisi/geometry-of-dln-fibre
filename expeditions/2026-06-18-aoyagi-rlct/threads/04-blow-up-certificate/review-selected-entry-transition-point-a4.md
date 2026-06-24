# Review - A4 selected-entry transition point

Date: 2026-06-24.

Reviewer: `James the 2nd`, xhigh-effort independent subagent.

Status: pass.  No blocking findings.

## Scope

Reviewed the current selected-entry transition-point slice:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-selected-entry-transition-point-a4.md`;
- `statement-card-a4-selected-entry-transition-point.md`.

The review checked for mathematical/formalisation mismatch, overclaiming,
bad denominator hypotheses, source overreach, and proof-hygiene issues.

## Findings

No blocking findings.

The reviewer confirmed that the Lean theorem uses the normalized target
coordinate as denominator hypothesis, not the finite center value.  In the
generic theorem the hypothesis is the nonzero value

```text
selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
  (chartEquiv targetChart).1 != 0,
```

and the Case 2 wrapper uses the corresponding
`case2SourceSelectedNormalizedMapOfMem` hypothesis.

The constructed target data matches the pen-and-paper reproduction:

```text
u_q = u*x_q,
y_e = x_e/x_q.
```

The reviewer also checked that the new docs keep the claim to finite
selected-entry transition-point algebra and explicitly exclude analytic atlas
coverage, transition regularity, source production, normal crossings, pole
order, and RLCT extraction.

## Gates

The reviewer reran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

Results:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

Full `DLNFibre` build completed successfully.  The emitted warnings are
pre-existing Core/style warnings outside this slice.

## Limitations

The reviewer did not edit files.  PDF text extraction tools were unavailable
in this VM, so the reviewer did not independently extract Aoyagi pp. 19-22
from the PDF.
