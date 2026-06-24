# Statement card - A4 Case 2 constructed old-top `Cprime` terminal-prefix source suffix

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSourceSuffix_entryIdeal_eq_constructedOldTopFromCprimeTerminalPrefixProduct_of_not_next_cont`

## Claim

Lean now specializes the stopped terminal-prefix source-suffix entry-ideal
consumer to the constructed old-top/free-`Cprime` source following factor.

The source side uses old-top rows `Cold` and the reconstructed old residual
block

```text
case2DisplayedPaperConstructedFollowingFactor ... Cprime
```

which is the finite `Q*Cprime` block.

The terminal side is the stopped-prefix reindexing of the source-row reindexing
of

```text
[Cold; case2DisplayedFreeCprimeTop ... Cprime].
```

The raw source suffix remains

```text
sourceSuffixProduct kappa Ctail S hSuffix.
```

## Proved

- The existing supplied terminal-prefix source-suffix consumer applies to the
  constructed old-top/free-`Cprime` following factor.
- The abstract terminal bridge is discharged by
  `SuppliedTerminalCprimeBridge.of_constructedWithOldTopFromCprime`.
- The source side is rewritten to `[Cold; Q*Cprime]`.
- The terminal side is rewritten to the double reindexing of
  `[Cold; top(Cprime)]`.

## Assumed

The finite displayed Case 2 supplied-boundary hypotheses, stopped
next-continuation `hstop`, arbitrary old-top rows `Cold`, arbitrary free
`Cprime`, and a supplied raw source suffix.

## Cited

None in Lean.  The source motivation is Aoyagi PDF pp. 21-22, where the
stopped Case 2 terminal product is displayed in terminal-prefix row order.

## Not Proved

No actual-width collapse, no original-row replacement of the transported pivot
row, no source production of `Csucc` or `C'^(S+1)`, no suffix construction, no
successor chart construction, no transition regularity, no chart coverage, no
normal crossings, no pole order, no termination, no RLCT, and no printed-vector
repair.

## Reproduction and Review

- Reproduction:
  `reproduction-case2-constructed-oldtop-cprime-terminal-prefix-source-suffix-a4.md`.
- Review:
  `review-case2-constructed-oldtop-cprime-terminal-prefix-source-suffix-a4.md`.

## Verification

- 2026-06-24, from `lean/`: `scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- 2026-06-24, from `lean/`: `scripts/lb DLNFibre` passed.
- 2026-06-24, from `lean/`: `scripts/sorries` reported
  `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- 2026-06-24, from expedition root: `git diff --check` passed.
