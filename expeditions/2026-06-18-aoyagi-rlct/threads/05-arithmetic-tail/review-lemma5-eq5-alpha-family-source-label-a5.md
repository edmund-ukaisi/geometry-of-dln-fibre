# Review - Lemma 5 equation (5) alpha-family source label

Status: reviewed and formalised.

## Scope

This slice connects the strict Eq5 alpha domain to the existing Eq5 label
legality theorem.  It adds no displayed-vector or source-coverage claim.

## Verdict

No findings.  The guard theorem is finite arithmetic, and the source-label
wrapper is a direct call to the existing
`aoyagiLemma5Eq5_actualWidthLabel_at_of_widthBound` after unpacking strict
alpha-domain membership.

## Xhigh Check

Source-slice scout `Avicenna` recommended this exact scope: use the alpha
domain to supply `1<=alpha` and `alpha<=excess`, keep `alpha<p` visible but do
not use it to claim branch existence or cutoff coverage.

## Nonclaims

This theorem does not construct an Eq5 vector, prove branch existence, derive
the cutoff guard, prove selected-span coverage, terminal `tilde t=0`, vector
admissibility, chart sequence, classifier/injection/back-to-label coverage,
Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
