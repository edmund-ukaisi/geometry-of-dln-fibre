# Review - Lemma 5 Eq5 early and tail interval guards

Status: reviewed and formalised.

## Scope

This slice identifies exact same-coordinate Htilde interval-membership guards
for the supplied Eq5 `preAlpha` and `alphaToP` branches, records automatic
membership for the `tail` branch, and proves that strict alpha-domain
membership supplies the two early-branch guards.

## Verdict

Survived.  No fidelity or soundness findings.  The statements stay at local
finite branch-value bookkeeping and do not claim source construction or
post-`p` repair.

## Checks

Focused Lean check passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

xhigh pen-and-paper scout `Lagrange` independently derived the branch offsets:
`b` for `preAlpha`, `alpha-1` for `alphaToP`, and no offset for `tail`.

Independent xhigh reviewer `Hypatia` confirmed the offsets against Aoyagi PDF
pp. 26-27 and Lean's zero-based indexing, and confirmed that the slice does
not overclaim source construction, source-label legality, terminality, chart
coverage, Lemma 5 count, pole order, normal crossings, or RLCT.

## Nonclaims

This theorem does not construct Eq5 vectors, prove source-label legality,
prove the post-`p` lower guard, prove terminal `tilde t=0`, chart coverage,
selected-span exactness, classifier/injection/back-to-label coverage, Lemma 5
order count, pole order, normal crossings, or RLCT extraction.
