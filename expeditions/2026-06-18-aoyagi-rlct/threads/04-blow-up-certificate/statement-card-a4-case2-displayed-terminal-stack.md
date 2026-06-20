# Statement card - A4 Case 2 displayed terminal stack

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`
- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.matrixEntryIdeal_sumElim_eq_sup`
- `DLNFibre.DLN.Aoyagi.matrixEntryIdeal_sumElim_congr_bottom`
- `DLNFibre.DLN.Aoyagi.matrixEntryIdeal_case2DisplayedPaperTerminalStack_eq_topStack_of_not_next_cont`

## Statement

Lean proves that stacking a fixed top row block over two lower blocks with
the same matrix-entry ideal preserves matrix-entry ideal equality.  Applying
this to the displayed Case 2 stopped terminal block gives:

```text
< entries([Cold; D''' * C']) >
  = < entries([Cold; C0]) >,
```

where `C0` is the top pivot row of the transported following factor
`C' = Q^-1 C`.

## Proved

- The matrix-entry ideal of a stacked row block is the supremum of the entry
  ideals of its two row blocks.
- Replacing the bottom block by any matrix with the same entry ideal preserves
  the stacked entry ideal.
- Under displayed Case 2 failed next continuation, the stack with bottom
  block `D''' * C'` has the same matrix-entry ideal as the stack with bottom
  block the top pivot row of `C'`.

## Assumed

- Displayed pivot validity and failed next continuation for the Case 2
  specialization.
- The old top block `Cold` is supplied as an arbitrary matrix with the same
  column type.
- The previous displayed paper terminal absorption theorem supplies the
  bottom-block entry-ideal equality.

## Not Proved

- No identification of `Cold` with the source's actual old top rows.
- No construction or identification of Aoyagi's next-stage `C'^(S+1)`.
- No diagonal-weighted full terminal product ideal.
- No source-order row-vs-column terminal presentation.
- No chart coverage, coordinate regularity, chart-produced recurrence or
  exponent post-data, Jacobian/volume arithmetic, normal crossings, RLCT
  extraction, termination theorem, transition invariant, or printed-vector
  repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-displayed-terminal-stack-a4.md`.
- Review artifact:
  `review-case2-displayed-terminal-stack-a4.md`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.EntryIdeal`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
