# Review - Lemma 5 Eq5 nonfirst block bounds

Status: reviewed/formalised; independent xhigh review survived.

## Scope

This slice unwraps the existing Eq5 nonfirst-block interval-membership theorem
into explicit same-coordinate Htilde bounds.  It requires a supplied Eq5
piecewise certificate, strict alpha-domain membership, the nonfirst condition
`1<=b`, block membership, and either the explicit post-`p` lower guard or the
terminal-room inequality.

## Verdict

No findings.  Independent xhigh reviewer `Pauli` checked that the Lean
theorems are conditional wrappers, not source constructions, and that the
reproduction and statement card keep the same limited scope.

## Checks

Focused Lean checks passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
```

Local hygiene before review:

```text
git diff --check
lean/scripts/sorries
```

The scanner reported `0 sorry`, `0 #exit`, `0 native_decide`, and `0 axiom`.

## Nonclaims

This theorem does not construct Eq5 vectors, prove source-label legality,
prove source branch coverage, prove the post-`p` guard from source hypotheses,
prove terminal `tilde t=0`, chart coverage, selected-span exactness,
classifier/injection/back-to-label coverage, Lemma 5 order count, pole order,
normal crossings, or RLCT extraction.
