# Review - Lemma 5 equation (5) offset/excess decomposition

Reviewers: `Pasteur the 2nd` (xhigh source/pen-and-paper scout) and
`Poincare the 2nd` (xhigh Lean/API scout).  Verdict: valid as finite count
bookkeeping.

## Findings

No issue was found with the decomposition statement.

The Eq5 strict-offset value set counts

```text
1 <= alpha <= min(excess(ell,a,p), p-1).
```

Thus its cardinality is `min(excess,p-1)`.  If the interval excess is rising
at coordinate `p`, i.e.

```text
1 <= p, p <= a, p <= ell-a,
```

then `excess(ell,a,p)=p`, so the strict Eq5 offsets count only `p-1` values
and one additional interval value remains.  If one of the rising inequalities
fails, the excess is at most `p-1`, so the strict offsets account for all of
the excess count.

The lower-endpoint exclusion is also correct: in the rising case,
`Htilde'_p-Htilde_p=p`; membership of `Htilde_p` in the strict offset set
would force `alpha=p`, contradicting `alpha<=p-1`.

## Source Fidelity

This slice should not be described as Aoyagi Lemma 5.  It is an arithmetic
decomposition of the same-coordinate interval count using the already-defined
Eq5 offset family.  It does not prove that Aoyagi's equations `(3)` or `(4)`
realise the remaining value, nor that equation `(5)` source vectors are
constructed or admissible.

## Checks

Controller check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

passed for the landed theorem draft before this review note was written.

## Residual Risks

The theorem is useful only as a scaffold for the order-count arithmetic.  The
main blockers remain displayed-vector construction, source-label legality at
all required layers, terminal `tilde t=0`, vector admissibility, Case 1(2)
chart sequence, pole order, normal crossings, and RLCT extraction.
