# Review - Lemma 5 equation (4) p=1 terminal extension obstruction

Status: pass.

Reviewer: xhigh independent audit, 2026-06-21.

## Scope Audited

- Lean declaration in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`:
  - `aoyagiLemma5Eq4_no_terminalUpperNatExtension_of_p1_sourceSelectedInequality`
- Reproduction note:
  `reproduction-lemma5-eq4-p1-terminal-extension-obstruction-a5.md`.
- Statement card:
  `statement-card-a5-lemma5-eq4-p1-terminal-extension-obstruction.md`.
- Thread, ledger, synthesis, claims, and priorities updates naming this
  checkpoint.

## Verdict

No findings.

The theorem is correctly scoped: it is conditional on a supplied equation `(4)`
piecewise certificate, the terminal-collision equality `1+1=a`, the
selected-sum identity, and strict selected-width inequalities.  It proves only
the incompatibility

```text
T (C.point ell - 1) != aoyagiHtildeUpperNat ell a M m ell.
```

The arithmetic is correct.  A supplied terminal upper-chain extension in the
`p=1` terminal-collision case would force `W_(ell+1)=M`.  Definition 3's
selected-width bound gives `W_(ell+1)<=M-1`, using `hT.a_le_ell` and
`1+1=a` to obtain `1<=ell`.  No extra positivity assumption is used.

## Nonclaims Checked

The checkpoint does not claim:

- construction or existence of equation `(4)`'s supplied certificate;
- construction of a terminal extension;
- terminal `tilde t=0`;
- Aoyagi Lemma 5 or its negation;
- Case 1(2) chart sequence, vector admissibility, or source-vector-to-chain
  correspondence;
- normal crossings or RLCT extraction.

## Verification

The reviewer reported passing:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
git diff --check
rg -n '\b(sorry|axiom|native_decide)\b|#exit' lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
rg -n '[ \t]+$' expeditions/2026-06-18-aoyagi-rlct/threads/05-arithmetic-tail/reproduction-lemma5-eq4-p1-terminal-extension-obstruction-a5.md expeditions/2026-06-18-aoyagi-rlct/threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-p1-terminal-extension-obstruction.md
```

The forbidden-token and trailing-whitespace scans returned no matches.

The reviewer did not run a full library build.
