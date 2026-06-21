# Review - Lemma 5 equation (4) boundary membership forces p

Status: pass.

Reviewer: xhigh independent audit, 2026-06-21.

## Scope Audited

- Lean declarations in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`:
  - `aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_forces_two_le_p_of_sourceSelected`
  - `aoyagiLemma5Eq4_boundaryValue_not_mem_boundaryInterval_of_sourceSelected_of_p_lt_two`
- Reproduction note:
  `reproduction-lemma5-eq4-boundary-membership-forces-p-a5.md`.
- Statement card:
  `statement-card-a5-lemma5-eq4-boundary-membership-forces-p.md`.
- Thread, ledger, synthesis, claims, and priorities updates naming this
  checkpoint.

## Verdict

No findings.

The Lean theorem proves only the necessary implication.  Boundary-coordinate
membership gives the lower width-window bound `M-p+1<=W_r`; the
source-selected Definition 3 inequality gives `W_r<=M-1`; `omega` derives
`2<=p`.  The `p<2` wrapper proves nonmembership by contradiction and does not
assert membership for `p>=2`.

The guards are appropriate.  No `p<=ell-a` guard or explicit `1<=ell`
hypothesis is needed: `p+1<a` plus the supplied certificate field `a<=ell`
give the boundary-coordinate range and `1<=ell`.

## Nonclaims Checked

The checkpoint does not claim:

- construction or existence of equation `(4)`'s displayed vector;
- membership for `p>=2`;
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
