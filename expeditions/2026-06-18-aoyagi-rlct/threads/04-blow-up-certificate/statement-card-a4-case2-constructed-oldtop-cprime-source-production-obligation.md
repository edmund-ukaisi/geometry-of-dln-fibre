# Statement card - A4 Case 2 constructed old-top `Cprime` source-production obligation

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceTerminalTransportedRows_constructedWithOldTopFromCprime_eq_terminalStack`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.of_constructedWithOldTopFromCprime_terminalStack`

## Claim

Lean now packages the constructed old-top/free-`Cprime` source following
factor into the existing `SourceProductionObligation` interface, with terminal
matrix equal to the source-row reindexing of

```text
[Cold; case2DisplayedFreeCprimeTop ... Cprime].
```

The source following factor is

```text
case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime
```

and the successor following factor stored in the obligation is the
formula-level

```text
case2DisplayedSourceSuccessorFollowingFactor ... C.
```

## Proved

- The constructed transported terminal rows are equal to the source-row
  reindexing of `[Cold; top(Cprime)]`.
- The canonical formula-level
  `SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`
  specializes to the constructed old-top/free-`Cprime` following factor after
  transporting along that terminal-row equality.

## Assumed

The displayed Case 2 supplied-boundary hypotheses, arbitrary old-top rows
`Cold`, arbitrary free `Cprime`, and a supplied raw source suffix family
`Ctail`.

## Cited

None in Lean.  The source motivation is Aoyagi PDF pp. 21-22, where the Case 2
formula-level transported following block is displayed.

## Not Proved

No actual-width collapse, no stopped-prefix theorem, no row-exhaustion theorem,
no source production of `Csucc` or `C'^(S+1)`, no suffix construction, no
successor chart construction, no transition regularity, no chart coverage, no
normal crossings, no pole order, no termination, and no RLCT consequence.

## Reproduction and Review

- Reproduction:
  `reproduction-case2-constructed-oldtop-cprime-source-production-obligation-a4.md`.
- Review:
  `review-case2-constructed-oldtop-cprime-source-production-obligation-a4.md`.

## Verification

- 2026-06-24, from `lean/`: `scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- 2026-06-24, from `lean/`: `scripts/lb DLNFibre` passed.
- 2026-06-24, from `lean/`: `scripts/sorries` reported
  `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- 2026-06-24, from expedition root: `git diff --check` passed.
