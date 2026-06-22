# Review - Lemma 5 Eq5 endpoint branch coordinates

Date: 2026-06-22.

Reviewer: xhigh `Chandrasekhar`.

Verdict: pass.  No mathematical/formalisation mismatches or doc overclaims
found after tightening the wording around lower endpoint insertion.

## Checks

- The raw proof splits exactly on `j <= a` and `j <= ell-a`; the lower endpoint
  coordinate hypothesis is used only in the rising lower-branch case.
- The filtered-family proof only extracts raw membership from
  `raw.filter (...)`, so it proves coordinate correctness only for surviving
  nonbase branches.
- No source-production, source-label legality, injectivity, disjointness,
  no-extra coverage, or classifier construction claim is introduced.
- No dedicated Eq5 counted-datum classifier wrapper was added.
- The markdown files are consistent with the Lean slice and with independence
  from the quiver paper.

## Residual Risk

The lower endpoint is explicitly inserted only in the rising branch.  Without
distinctness hypotheses, `lower j` could still occur in the non-rising raw
finset by collision with `upper j` or a strict branch.  The formal proof
handles that through the upper/strict alternatives and does not assert
distinctness or survival.
