# Review - Lemma 5 equation (4) terminal extension forces p

Status: pass.

Reviewer: xhigh independent audit, 2026-06-21.

## Scope Audited

- Lean declarations in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`:
  - `aoyagiLemma5Eq4_terminalExtension_forces_two_le_p_of_sourceSelected`
  - `aoyagiLemma5Eq4_no_terminalExtension_of_sourceSelected_of_p_lt_two`
- Reproduction note:
  `reproduction-lemma5-eq4-terminal-extension-forces-p-a5.md`.
- Statement card:
  `statement-card-a5-lemma5-eq4-terminal-extension-forces-p.md`.
- Thread, ledger, synthesis, claims, and priorities updates naming this
  checkpoint.

## Verdict

No findings.

The theorem pair is correctly scoped.  A supplied terminal upper-chain
extension plus terminal-collision equation `(4)` forces
`W_(ell+1)=M-p+1`; Definition 3's selected-width hypotheses give
`W_(ell+1)<=M-1`; hence `2<=p`.  The companion theorem says that, under the
same supplied-certificate and source-selected hypotheses, `p<2` rules out the
supplied terminal upper-chain extension.

The statement records the `p=0` case only as a Lean-totalized
supplied-certificate edge, not as an additional printed source case.

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
rg -n '[ \t]+$' expeditions/2026-06-18-aoyagi-rlct/threads/05-arithmetic-tail/reproduction-lemma5-eq4-terminal-extension-forces-p-a5.md expeditions/2026-06-18-aoyagi-rlct/threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-terminal-extension-forces-p.md
```

The forbidden-token and trailing-whitespace scans returned no matches.

The reviewer did not run a full library build.
