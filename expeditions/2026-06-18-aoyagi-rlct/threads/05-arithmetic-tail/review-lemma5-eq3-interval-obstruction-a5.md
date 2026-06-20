# Review - A5 Lemma 5 equation (3) interval obstruction

Status: pass.

Reviewer: xhigh independent audit, 2026-06-20.

## Scope Audited

- Lean declarations in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`:
  - `aoyagiLemma5Eq3_boundaryValue_gt_upperNat`
  - `aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat`
  - `aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat_of_two_le`
- Reproduction note:
  `reproduction-lemma5-eq3-interval-obstruction-a5.md`.
- Statement card:
  `statement-card-a5-lemma5-eq3-interval-obstruction.md`.
- Thread, ledger, synthesis, priorities, and claims updates naming this
  checkpoint.

## Verdict

No findings.

The Lean statements are sound for the stated finite interval bookkeeping.
They use the supplied equation `(3)` boundary assignment
`Htilde'_(ell-a+1)+1` and the existing same-coordinate interval-value-set API
to show that the boundary value is above the upper endpoint of that interval.

## Source Fidelity

Aoyagi PDF p. 27 supports the displayed equation `(3)` boundary assignment.
The checkpoint does not claim that the printed family constructs a full source
vector or terminal chart sequence; it only records the finite value-set
exclusion below that boundary.

## Nonclaims Checked

The checkpoint does not claim:

- displayed-vector construction;
- terminal `tilde t=0`;
- introduced-label status;
- vector admissibility;
- Case 1(2) chart sequence;
- Lemma 5 order count;
- normal crossings or RLCT extraction.

## Verification

The reviewer reported passing:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
git diff --check
```

The reviewer also scanned the changed Lean file for proof-hole and unsafe
tokens and checked the new reproduction/card docs for trailing whitespace and
source-scope overclaims.
