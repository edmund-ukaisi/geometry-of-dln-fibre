# Statement card - A5 Lemma 5 first-nonbase cardinal bound

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le`

## Claim

For a finite supplied candidate set with terminal chains satisfying the
terminal binary-prefix-delta hypotheses, the deterministic
first-nonbase-or-base selector gives the displayed Aoyagi Lemma 5 upper count
provided that the selector is injective on candidates.

## Proved

The selector maps every supplied candidate into
`aoyagiLemma5CountDatumSet` by the existing terminal first-nonbase maps-to
theorem. With supplied injectivity, the candidate set has the same cardinality
as its selector image; the image is contained in the counted datum set; and
the counted datum set has cardinality `a*(ell-a)+1`.

## Assumed

The theorem assumes `1 <= ell`, `a <= ell`, terminal endpoint data for every
candidate chain, the selected-width sum `sum_i m_i = ell*(M-1)+a`, binary
prefix deltas for every candidate chain, interval membership of the supplied
base values, and injectivity of the deterministic selector on the candidate
set.

## Cited

None. This is finite set bookkeeping, using already-formalised A5 interval
counting and terminal binary maps-to lemmas.

## Deferred

No source vector construction, no canonical source classifier, no injectivity
proof, no back-to-label or no-extra terminal-minimum theorem, no Eq3/Eq4/Eq5
branch construction, no finite minimum-to-`lambda` equality, no pole order, no
normal crossings, and no RLCT extraction.

## Review

Focused Lean check passed for `DLNFibre.DLN.Aoyagi.Lemma5SuppliedFamily`.
Independent xhigh reviewer `Kierkegaard the 2nd` found no issues.  Residual
source-boundary assumptions are construction of the candidate terminal chains
`H`, proof of the binary-prefix-delta hypotheses from Aoyagi's vectors,
base-branch/base-value realisation, injectivity of this selector, no-extra
terminal-minimum coverage, and counted-datum back-to-label data.

Review artifact:
`review-lemma5-first-nonbase-cardinal-bound-a5.md`.
