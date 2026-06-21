# Review - Lemma 5 equation (5) interval erase-upper equality

Reviewers: controller review; exact-diff reviewer pending.
Verdict before exact-diff return: finite-set equality is source-faithful.

## Findings

No issue was found in the controller check.

The equality follows from three already-controlled pieces:

```text
inserted set subset interval
card(inserted set)+1 = card(interval)
upper endpoint in interval and not in inserted set
```

The upper endpoint nonmembership is correct.  In the rising region the gap
`Htilde'_p-Htilde_p` is `p>=1`, so the upper endpoint is distinct from the
lower endpoint.  Membership in the strict offset set would require
`Htilde'_p = Htilde'_p-alpha`, hence `alpha=0`, contradicting `alpha>=1`.

## Source Fidelity

The theorem identifies a finite-set complement inside the same-coordinate
interval.  It does not say that the erased upper endpoint is realised by any
displayed vector or chart.

## Checks

Controller check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

passed before this note was written.

Exact-diff xhigh reviewer verdict: pass, with the cwd clarification above.

## Residual Risks

This is still count-side scaffolding.  It does not prove displayed-vector
construction, terminal `tilde t=0`, vector admissibility, chart sequence,
normal crossings, or RLCT extraction.
