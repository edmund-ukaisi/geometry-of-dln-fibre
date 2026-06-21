# Review - Lemma 5 Eq5 endpoint prefix profile

Status: reviewed/formalised; low documentation finding fixed.

## Scope

This slice proves branchwise Lemma 4 increment-prefix values for a supplied
Eq5 piecewise vector and supplied endpoint-chain correspondence.  The
alpha-to-`p` and post-`p` branch profiles also require terminal-room.

## Findings

Low, fixed: the first ledger-style summaries did not mention that the
alpha-to-`p` and post-`p` theorems require terminal-room.  The formal Lean
statements, reproduction note, and statement card already had this hypothesis;
the thread, synthesis, and theorem-ledger summaries were tightened to match.

## Verdict

No formal arithmetic findings.  Independent xhigh reviewer `James` checked
that the branch formulas match the supplied Eq5 branch equalities, that
terminal-room is used only for the alpha-to-`p` and post-`p` high-count
collapse, and that import-cycle risk is low.

## Checks

Focused Lean checks passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5EndpointProfile.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5Eq5EndpointProfile
lake env lean DLNFibre.lean
```

## Nonclaims

This slice does not prove adjacent-branch binary deltas, Lemma 4 two-value
increments, Eq5 vector construction, endpoint realisation, terminality,
classifier data, order count, pole order, normal crossings, or RLCT extraction.
