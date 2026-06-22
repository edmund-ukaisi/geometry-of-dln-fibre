# Statement card - A5 Lemma 5 Eq5 own-block counted/introduced payload

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_widthBound`

## Claim

For one supplied equation `(5)` own-block branch, an explicit nonbase
hypothesis maps its own-block value into `aoyagiLemma5CountDatumSet`, and the
same branch gives the corresponding introduced source label.

## Proved

Lean combines two existing one-branch facts.  The Eq5 own-block source-label
wrapper gives `T S = k - 1` and
`Sigma.mk S k ∈ introducedLabelFinset L n S k`.  The interval membership part
of that wrapper, together with `1 <= p`, `C.block p S`, and the supplied
inequality `T S != baseValue p`, gives
`some (Sigma.mk p (T S)) ∈ aoyagiLemma5CountDatumSet ell a M m baseValue`.

## Assumed

The theorem assumes a supplied Eq5 piecewise certificate, the selected-width
sum, source inequality, source-range bound `C.point ell <= L+1`, actual-width
lower bound at `S`, label formula
`k = Htilde'_p + 1 - alpha`, positive coordinate `1 <= p`, own-block
membership `C.block p S`, and nonbase status `T S != baseValue p`.

## Deferred

Eq5 vector construction, proof of nonbase status, alpha-domain coverage,
endpoint-chain realisation, classifier construction, injection, back-to-label
coverage, no-extra terminal-minimum coverage, order count, pole order, normal
crossings, and RLCT extraction.

## Review

Focused Lean check, module build, full `DLNFibre` build, aggregator check,
`git diff --check`, and `scripts/sorries` passed.  Independent xhigh review is
recorded in `review-lemma5-eq5-ownblock-counted-introduced-payload-a5.md`.
