# Review - Lemma 5 equation (4) no terminal upper extension example

Status: pass.

Reviewer: xhigh independent audit, 2026-06-21.

## Scope Audited

- Lean declaration in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`:
  - `aoyagiLemma5Eq4_no_terminalUpperNatExtension_ell3_a2_p1_allWidthsTwo`
- Reproduction note:
  `reproduction-lemma5-eq4-no-terminal-upper-extension-example-a5.md`.
- Statement card:
  `statement-card-a5-lemma5-eq4-no-terminal-upper-extension-example.md`.
- Thread, ledger, synthesis, claims, and priorities updates naming this
  checkpoint.

## Verdict

No findings.

The theorem is correctly scoped: it is conditional on a supplied
`AoyagiLemma5Eq4PiecewiseSourceVector` for
`ell=3`, `a=2`, `p=1`, `M=3`, and all selected widths equal to `2`, and proves
only incompatibility with the supplied terminal upper-chain extension
`T(C.point 3 - 1)=Htilde'_3`.

The arithmetic is correct: the selected sum is `8`, the target
`ell*(M-1)+a` is `3*(3-1)+2=8`, the strict selected-width inequality reads
`3*2<8`, the terminal-collision index is `p+(ell-a)+1=3=ell`, the last width
is `2`, the compatibility target is `M-p+1=3`, the equation `(4)` terminal
branch value is `1`, and the upper terminal endpoint is `0`.

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
```

The forbidden-token scan returned no matches.  The reviewer also checked the
new untracked docs for trailing whitespace.

The reviewer did not run a full library build.
