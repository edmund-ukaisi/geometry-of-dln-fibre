# Statement card - A4 Case 2 constructed old-top `Cprime` terminal prefix

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimePrefixCandidate_constructedWithOldTopFromCprime_eq_terminalStackPrefix`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalProductPrefixCandidate_constructedWithOldTopFromCprime_eq_weight_mul_terminalStackPrefix_mul`

## Claim

Lean now specializes the stopped terminal-prefix `Cprime` candidate and
terminal-prefix product candidate to the constructed old-top/free-`Cprime`
source following factor.

Under

```text
hstop : not (J+2 <= prefixMinNat n (S+1)),
```

the terminal-prefix `Cprime` candidate is the terminal-prefix reindexing of
the source-row matrix

```text
[Cold; case2DisplayedFreeCprimeTop n hS hcont Cprime].
```

The stopped terminal-prefix product candidate rewrites to

```text
(case2DisplayedSourceTerminalWeightPrefixCandidate Wold n hcont hstop b0 *
  explicitPrefixRows) * F.
```

## Proved

- The explicit constructed source-row terminal matrix from the previous slice
  reindexes to terminal-prefix rows under `case2SourceTerminalRowEquivPrefixOfNotNext`.
- The stopped terminal-prefix `Cprime` candidate for the constructed factor is
  exactly that reindexed matrix.
- The stopped terminal-prefix product candidate consumes the same explicit
  prefix matrix.

## Assumed

The finite displayed Case 2 formation hypotheses, the stopped-prefix
hypothesis `hstop`, and arbitrary matrices `Cold`, `Cprime`, `Wold`, and `F`.

## Cited

None in Lean.  The source motivation is Aoyagi PDF pp. 21-22, where the
stopped Case 2 terminal product is displayed in terminal-prefix row order.

## Not Proved

No actual-width collapse, no original-row replacement of the transported pivot
row, no source-produced `C'^(S+1)`, no terminal chart construction, no suffix
production, no transition regularity, no chart coverage, no normal crossings,
no pole order, no termination, no RLCT, and no printed-vector repair.

## Reproduction and Review

- Reproduction:
  `reproduction-case2-constructed-oldtop-cprime-terminal-prefix-a4.md`.
- Review:
  `review-case2-constructed-oldtop-cprime-terminal-prefix-a4.md`.

## Verification

- 2026-06-24, from `lean/`: `scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- 2026-06-24, from `lean/`: `scripts/lb DLNFibre` passed.
- 2026-06-24, from `lean/`: `scripts/sorries` reported
  `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- 2026-06-24, from expedition root: `git diff --check` passed.
