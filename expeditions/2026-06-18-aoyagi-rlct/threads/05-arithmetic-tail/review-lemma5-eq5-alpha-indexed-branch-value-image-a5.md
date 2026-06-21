# Review - Lemma 5 equation (5) alpha-indexed branch value image

Status: reviewed and formalised.

## Scope

This slice packages a supplied finite branch family whose alpha projection is
exactly the strict Eq5 alpha domain and whose branch values are
`Htilde'_p-alphaOf b`.

## Verdict

Survived.  No fidelity or soundness findings.  The theorem is finite-set image
bookkeeping and its hypotheses keep all source-production work explicit.

## Checks

Focused Lean checks passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
```

The proof does not use injectivity.  This is appropriate: duplicate branches
with the same alpha or value do not affect the image equality.

Independent xhigh reviewer `Anscombe` confirmed that
`aoyagiLemma5Eq5AlphaDomain` matches the strict Eq5 alpha guards
`1<=alpha`, `alpha<=Htilde'_p-Htilde_p`, and `alpha<p`, and that the branch
bridge stays at the intended finite-image level.

## Nonclaims

This theorem does not construct branch records, equation `(5)` displayed
vectors, source labels, cutoff guards, selected-span coverage, terminal
`tilde t=0`, branch injectivity, classifiers, back-to-label coverage, Lemma 5
order count, pole order, normal crossings, or RLCT extraction.
