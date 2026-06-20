# Review - A5 Lemma 5 interval-excess arithmetic

Reviewed objects:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`
- `reproduction-lemma5-interval-excess-a5.md`
- `statement-card-a5-lemma5-interval-excess.md`

Verdict: no blocking arithmetic or scope issue found for the isolated
interval-excess sub-slice.

Independent xhigh pen-and-paper checker `Confucius the 5th` verified the
excess-cardinality identity

```text
sum_{j=1}^{ell-1} (|I_j|-1) = a(ell-a),
```

and the source-facing form

```text
1 + sum_{j=1}^{ell-1} (|I_j|-1) = a(ell-a)+1.
```

The checker emphasized that the raw sum of `|I_j|` is not the desired count,
and that including `j=ell` changes nothing because the top excess is zero.
Endpoint behavior `a=0`, `a=ell`, and `ell=1` was checked.

Independent xhigh Lean scout `Maxwell the 5th` recommended the rectangle-fiber
proof now implemented: identify each closed excess with a fiber of
`range a x range (ell-a)` under `(p,q) |-> p+q+1`, then sum fibers to count the
rectangle.

This must not be presented as Lemma 5 itself.  It proves only finite
interval-size arithmetic.  It does not prove chart-family admissibility,
coverage, the displayed vector constructions, pole-order counting, normal
crossings, or RLCT extraction.

Controller verification ran
`lake env lean DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`.
