# Review - Lemma 5 equation (4) p=2 boundary membership example

Status: pass.

Reviewer: xhigh independent audit, 2026-06-21.

## Scope Audited

- Lean declaration in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`:
  - `aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_p2_constantWidth_example`
- Reproduction note:
  `reproduction-lemma5-eq4-boundary-membership-p2-example-a5.md`.
- Statement card:
  `statement-card-a5-lemma5-eq4-boundary-membership-p2-example.md`.
- Thread, ledger, synthesis, claims, and priorities updates naming this
  checkpoint.

## Verdict

No findings.

The arithmetic is correct: for `ell=5`, `a=4`, `p=2`, `M=5`, and all selected
widths equal to `4`, the selected-width sum is `24`, the target sum
`ell*(M-1)+a` is also `24`, the strict selected-width inequality reads
`5*4<24`, the boundary coordinate is `r=4`, and the boundary-coordinate width
window is `4<=W_r<=5`.

The Lean theorem remains conditional on a supplied equation `(4)` certificate.
It does not construct that certificate or the displayed vector.

The caveat that the example fails `p<=ell-a` is accurate and not harmful: that
guard belongs to the older own-coordinate classifier at coordinate
`p+(ell-a)`, not to the boundary-coordinate theorem.

## Nonclaims Checked

The checkpoint does not claim:

- construction or existence of equation `(4)`'s supplied certificate;
- construction of equation `(4)`'s displayed vector;
- terminal `tilde t=0`;
- introduced-label status, vector admissibility, or the Case 1(2) chart
  sequence;
- Lemma 5 order count;
- normal crossings or RLCT extraction.

## Verification

The reviewer reported passing:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
git diff --check
```

The reviewer did not run a full library build.
