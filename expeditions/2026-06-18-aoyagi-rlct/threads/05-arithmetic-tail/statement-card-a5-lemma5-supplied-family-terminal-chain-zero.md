# Statement Card - A5 Lemma 5 Supplied Family Terminal Chain Zero

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleNonbaseFamily.branch_terminalH_zero`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleFamily.base_terminalH_zero`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalH_zero`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryNonbaseFamily.branch_terminalH_zero`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryFamily.base_terminalH_zero`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalH_zero`

## Claim

Every supplied admissible or binary Lemma 5 branch has terminal chain value
zero.  For full families, this holds uniformly for the tagged base branch
`none` and for tagged nonbase branches `some b`.

## Inputs

- For admissible families: the supplied `Htilde` chain bounds, `a <= ell`, and
  the selected-width sum.
- For binary families: the supplied terminal fields `Hlast` and `baseHlast`.
- Membership of the tagged branch in the supplied full branch set.

## Proves

- Nonbase admissible branch chains satisfy `H(b)(Fin.last ell) = 0`.
- The admissible base chain satisfies `baseH(Fin.last ell) = 0`.
- Every tagged admissible full branch satisfies
  `fullH x (Fin.last ell) = 0`.
- The analogous binary-family statements follow directly from supplied
  terminal fields.

## Does Not Prove

- A source-vector terminal equality `T(C.point ell - 1)=0`.
- Construction of the terminal/base source branch.
- Source-label legality, classifier exactness, injection, back-to-label
  coverage, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 4/Lemma 5 terminal chain endpoint arithmetic, PDF pp. 25-26.  The
source supports `Htilde_ell=Htilde'_ell=0`; the source does not by itself
provide the source-coordinate terminal branch used by the separate Eq5 terminal
coverage wrapper.
