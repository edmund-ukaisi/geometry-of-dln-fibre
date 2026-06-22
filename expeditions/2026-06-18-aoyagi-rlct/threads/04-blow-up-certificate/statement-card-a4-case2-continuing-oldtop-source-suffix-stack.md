# Statement Card - A4 Case 2 Continuing Old-Top/Source-Suffix Stack

## Lean Name

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withCorrectedPostData`

## Claim

In the displayed Case 2 continuing branch, the supplied paper `Q/P` identity
can be lifted through the unchanged old top rows and multiplied by the actual
source suffix.  The result is a pivot-first stack identity with the transported
paper factor `C' = Q^-1 C`.

## Proved

Lean proves an exact matrix equality after right multiplication by
`sourceSuffixProduct`, together with:

- next residual-center nonemptiness under `J+2 <= prefixMinNat n (S+1)`;
- corrected post exponent certificates;
- post level invariants, least-value gap, and recurrence Case 2 gap;
- finite current-center principalization by `u`.

## Assumed

The theorem keeps the common displayed Case 2 source-chart hypotheses explicit:
pre exponent certificates, level invariants, least-value gap, residual
chart-family boundary, continuation and next-continuation bounds, and source
suffix data.

## Deferred

Source production of a source-ordered successor `C'^(S+1)`, source production
of the suffix, chart coverage, arbitrary pivot coverage, transition
invariance, Jacobian arithmetic, normal crossings, pole order, termination,
and RLCT extraction.

## Review

- Pen-and-paper scout `Kepler` warned that full source production remains
  supplied-boundary-only; this theorem follows that boundary by keeping paper
  `C'` in pivot-first order.
- Lean/API scout `Boyle` confirmed that old-top/source-suffix continuing stack
  data were not already present and would be non-redundant if it included old
  top rows and the transported pivot row.
- Focused Lean check and module build passed for
  `DLNFibre.DLN.Aoyagi.BlowupArithmetic`.
- Independent xhigh reviewer `Russell` found no fidelity or overclaiming
  issues and recommended banking.
