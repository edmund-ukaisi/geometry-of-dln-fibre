# Statement Card - A5 Lemma 5 Terminal Source Bridge

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_Eq5Coverage`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_Eq5Coverage`

## Claim

If a supplied full-family branch is explicitly realised at the terminal source
coordinate, then its terminal chain-zero theorem supplies the terminal zero
needed by the Eq5 terminal finite-set wrapper.

## Inputs

- A supplied admissible or binary full branch family.
- A tagged branch `x in fullBranches`.
- The selected-width sum and `a<=ell`.
- An explicit source-realisation equality
  `T(C.point ell - 1)=fullH x (Fin.last ell)`.

## Proves

```text
insert T(C.point ell - 1) Eq5Offsets_ell = Interval_ell.
```

## Does Not Prove

- The source-realisation equality.
- Construction of a terminal/base source branch.
- Source-label legality, terminal-label exactness, classifier coverage,
  injection, back-to-label coverage, pole order, normal crossings, or RLCT
  extraction.

## Source

Aoyagi Lemma 5 terminal endpoint arithmetic, PDF pp. 25-27.  The bridge is a
conditional Lean interface: it records the exact additional source-coordinate
hypothesis needed to use the already-proved terminal chain endpoint.
