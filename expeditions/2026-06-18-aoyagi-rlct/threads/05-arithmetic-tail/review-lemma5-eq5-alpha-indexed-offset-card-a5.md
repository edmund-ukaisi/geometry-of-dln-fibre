# Review - Lemma 5 Eq5 alpha-indexed offset cardinality

Reviewer: xhigh `Huygens`.

Scope:

- `aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_eq_offsetValueSet_card`;
- proposed alpha-domain coverage cardinality bridge.

## Findings

None blocking.

## Verdict

Pass.  The theorem is mathematically honest as a finite cardinality bridge:
both sides are counted through the same strict alpha domain.  It does not
assert that the Sigma-valued label image equals the integer offset-value set.
This distinction matters because the branch label has second coordinate
`Htilde'_p+1-alpha`, while `aoyagiLemma5Eq5OffsetValueSet` contains the
integer values `Htilde'_p-alpha`.

The theorem packages existing ingredients: branch-label image cardinality from
supplied alpha injectivity and the label formula, supplied alpha-domain image
coverage, and injectivity of `alpha |-> Htilde'_p-alpha` for the offset-value
set.

## Commands Run

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`
- local read-only `rg`/`sed` inspections

## Residual Risk

The alpha-image hypothesis is strong supplied coverage data.  This review did
not construct that data from Aoyagi's printed equations and did not re-audit
the upstream alpha-domain arithmetic beyond this finite-cardinality boundary.
