# Review - Lemma 5 Eq5 Terminal-Room Guard

Reviewer: xhigh independent reviewer `Halley`.

## Verdict

No findings.  The slice is worth banking.

## Checks

- The theorem
  `aoyagiLemma5Eq5PostPLowerGuard_iff_terminalRoom_of_alphaDomain` states
  exactly the proved finite arithmetic: under strict Eq5 alpha-domain
  membership, the global post-`p` lower guard is equivalent to
  `p+2*a-alpha<=ell`.
- The reverse direction is sound: the endpoint
  `b=p+(a-alpha)` is a legitimate post-`p` coordinate, and the equality
  `alpha+b-p=a` uses the alpha-domain consequence `alpha<=a`, not unsafe
  truncated subtraction.
- The forward direction properly relies on the existing sufficient
  terminal-room theorem after extracting `alpha<=p` and `alpha<=a` from the
  strict alpha domain.
- The nonfirst-block wrapper retains the supplied Eq5 piecewise certificate
  and block hypotheses.

## Nonclaims Checked

The names and docstrings do not claim source construction, chart coverage,
classifier exactness, pole order, normal crossings, or RLCT extraction.

## Verification

The reviewer ran:

```text
lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
```

from `lean/`; it passed.
