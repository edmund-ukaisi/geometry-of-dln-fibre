# Statement card - A5 Lemma 5 terminal binary first-nonbase selector

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5InteriorNonbaseCoordSet`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_mem_of_terminalH_binaryIncrementPrefixDelta`

## Claim

The finite selector that chooses the least interior coordinate where a supplied
terminal chain differs from the supplied base values, or `none` if there is no
such coordinate, maps into Aoyagi Lemma 5's counted-datum codomain under the
same terminal binary-prefix-delta hypotheses used by the one-coordinate
maps-to theorem.

## Proved

If the nonbase-coordinate filter is empty, the selector returns `none`, which
belongs to the counted-datum set by insertion.  If it is nonempty, `Finset.min'`
gives a filtered interior coordinate, the filter gives the non-base-value
inequality, and
`aoyagiLemma5CountDatumSet_mem_of_terminalH_binaryIncrementPrefixDelta`
proves membership for the selected coordinate-value datum.

## Assumed

The theorem assumes `a <= ell`, `H 0 = m 0`, terminal value
`H (Fin.last ell)=0`, the selected-width sum
`sum_i m_i = ell*(M-1)+a`, and binary prefix deltas for the supplied chain
`H`.

## Deferred

No source vector construction, no canonical source classifier, no injection,
no back-to-label map, no no-extra terminal-minimum theorem, no Eq3/Eq4/Eq5
branch construction, no pole order, no normal crossings, and no RLCT
extraction.

## Review

Focused Lean check passed for `DLNFibre.DLN.Aoyagi.Lemma5SuppliedFamily`.
Independent xhigh reviewer `Poincare the 4th` found no blocking issue and
confirmed that the slice proves only finite maps-to membership, not a
classifier, injection, or exactness theorem.
