# Review - Lemma 5 Eq5 nonfirst block admissibility

Status: reviewed/formalised; independent xhigh review survived.

## Scope

This slice assembles already-proved local Eq5 branch interval-membership facts
into a supplied nonfirst-block admissibility wrapper.  It requires strict
alpha-domain membership and keeps the post-`p` lower guard explicit.

## Verdict

No findings.  The statement excludes the first branch and does not claim source
construction or source-derived post-`p` guard production.  Independent xhigh
reviewer `Confucius` found no fidelity or claim-soundness break.

## Checks

Focused Lean check passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

xhigh pen-and-paper scout `Faraday` validated the exact theorem shape and kill
conditions.

Independent xhigh reviewer `Confucius` checked that the theorem covers exactly
the nonfirst Eq5 branches `preAlpha`, `alphaToP`, `postP`, and `tail`; that
`postP` admissibility remains the explicit hypothesis
`aoyagiLemma5Eq5PostPLowerGuard`; and that live-source axiom reporting for the
target contains only the ordinary classical/quotient axioms
`propext`, `Classical.choice`, and `Quot.sound`.

## Nonclaims

This theorem does not construct Eq5 vectors, prove source-label legality,
prove source branch coverage, prove the post-`p` guard from source hypotheses,
prove terminal `tilde t=0`, chart coverage, selected-span exactness,
classifier/injection/back-to-label coverage, Lemma 5 order count, pole order,
normal crossings, or RLCT extraction.
