# Review - A4 Case 2 source-selected Schur complement

Date: 2026-06-24.

Reviewer: xhigh independent reviewer `Noether the 2nd`; controller gate.

Verdict: pass, with source-access caveat.

## Scope Reviewed

- Lean diff in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`;
- new theorem statements and docstrings:

```text
pivotFirstSchurComplement_apply
selectedEntryNormalizedMap_schurComplement_transition_mul_sq
case2SourceSelectedNormalizedBlockOfMem_schurComplement_apply
```

## Findings

No blocking soundness, subtype/source-coordinate, denominator, or overclaiming
issue was found.

The reviewer confirmed that `pivotFirstSchurComplement_apply` is exactly the
entrywise `D - x*y` identity; the denominator-cleared overlap theorem has the
needed nonzero normalized-coordinate hypothesis; and the Case 2 wrapper
projects through the residual-block subtypes using supplied pivot membership.

The review did not use the quiver paper.  The reviewer could not directly
extract Aoyagi PDF pp. 20-21 in the subagent environment, so its source-fidelity
check is against the local Aoyagi-specific reproduction notes and Lean block
algebra rather than direct PDF text.  The controller pen-and-paper reproduction
and the separate xhigh source scout supplied the page-based check for this
finite calculation.

## Verification

The reviewer ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
```

The controller additionally ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build still reports pre-existing unrelated Core/style
warnings.
