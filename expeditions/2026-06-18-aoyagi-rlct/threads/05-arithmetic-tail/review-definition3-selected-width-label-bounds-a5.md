# Review - Definition 3 selected-width label bounds

Reviewer: xhigh `Franklin`.

Status: passed after wording polish.

## Findings

No blocking issues.

Minor wording issue: the theorem-ledger entry initially said the full label
bound holds "under Definition 3's selected-width hypotheses" without naming
the label-position guards.  The Lean theorem also assumes `1<=p`, `p<=a`,
`1<=ell`, and `a<=ell`.  The surrounding notes stated this correctly.

## Checks

- The tail estimate is correct.  Lean's `aoyagiPrefixSum w p` is the
  inclusive zero-based prefix, i.e. source `P_(p+1)`.
- The tail `Finset.Ico (p+1) (ell+1)` is exactly the selected widths after
  `P_(p+1)` and has `ell-p` terms.
- The proof of `P_(p+1) >= p*(M-1)+a >= pM` uses `p<=a` and no hidden
  positivity assumption on `M`.
- The lower positivity theorem correctly does not require `1<=p`; the
  combined label-bound theorem does, because the upper half needs the
  previous-prefix slack.
- The notes do not overclaim displayed-vector realisation, selected-index
  guards, terminal `tilde t=0`, or Lemma 5 order count.

## Verification

Reviewer reported:

```text
lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean
git diff --check
```
