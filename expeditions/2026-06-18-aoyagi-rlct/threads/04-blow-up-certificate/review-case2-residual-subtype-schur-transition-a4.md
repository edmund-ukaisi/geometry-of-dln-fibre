# Review - A4 Case 2 residual-subtype Schur transition

Date: 2026-06-24.

Reviewers: xhigh source scout `Hilbert the 2nd`, xhigh Lean API scout
`Zeno the 2nd`, and controller gate.

Verdict: pass.

## Scope Reviewed

- Proposed residual-subtype adapter shape for
  `case2SourceSelectedNormalizedBlockOfMem_schurComplement_transition_mul_sq`;
- Lean implementation in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`;
- reproduction and statement-card boundaries.

## Findings

The scouts agreed that the adapter is source-faithful bookkeeping, not new
source content.  It changes ambient off-pivot row and column complements to
residual-row and residual-column subtype complements and reads their source
labels as `i.1.1` and `j.1.1`.  The load-bearing denominator remains the
normalised target coordinate, not `u` times that coordinate.

The API scout independently proposed the same theorem shape and the same
subtype-to-ambient complement conversion used by the implementation:

```lean
⟨i.1.1, by intro h; exact i.2 (Subtype.ext (by simpa using h))⟩
```

and similarly for columns.

## Verification

Gates:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

passed.  The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`,
and `0 axiom`.  The full build has pre-existing unrelated Core/style warnings.
