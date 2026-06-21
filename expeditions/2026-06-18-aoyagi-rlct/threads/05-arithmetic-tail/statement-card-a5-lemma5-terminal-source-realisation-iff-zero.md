# Statement Card - A5 Lemma 5 Terminal Source Realisation Iff Zero

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_realisation_iff_terminalZero`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_realisation_iff_terminalZero`

## Claim

For a supplied full-family branch with terminal chain value zero, the terminal
source-realisation equality

```text
T(C.point ell - 1) = F.fullH x (Fin.last ell)
```

is equivalent to the supplied terminal source-zero equality

```text
T(C.point ell - 1) = 0.
```

## Inputs

- A supplied admissible or binary full branch family.
- A tagged branch `x in fullBranches`.
- In the admissible case: `a<=ell` and the selected-width sum.

## Proves

The equivalence between terminal source realisation and terminal source zero.

## Does Not Prove

- Terminal source zero.
- Source-realisation equality from branch-family data alone.
- Construction of a terminal/base source branch.
- Terminal-label exactness, classifier coverage, pole order, normal crossings,
  or RLCT extraction.

## Source

Aoyagi Lemma 5 terminal endpoint arithmetic, PDF pp. 25-27.  This slice is
only Lean bookkeeping around the existing supplied branch-chain terminal-zero
theorems.
