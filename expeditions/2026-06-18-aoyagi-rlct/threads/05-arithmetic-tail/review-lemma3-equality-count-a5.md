# Review - A5 Lemma 3 equality count

Reviewed objects:

- `lean/DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`
- `reproduction-lemma3-equality-count-a5.md`
- `statement-card-a5-lemma3-equality-count.md`

Verdict: no blocking arithmetic or scope issue found for the isolated
finite-count sub-slice.

Independent xhigh pen-and-paper checker `Lagrange the 5th` verified that,
under `1 <= ell` and `0 <= a <= ell`, the equality set over
`0 <= b <= ell-1` has:

```text
a = 0:        one value, b=0;
0 < a < ell: two values, b=a-1 and b=a;
a = ell:      one value, b=ell-1.
```

The checker also confirmed the edge case `ell=1`: the strict interior is empty
and each endpoint leaves the single source value `b=0`.

Independent xhigh Lean scout `Leibniz the 5th` recommended the helper
`aoyagiLemma3AMinimizerSet`, endpoint/interior set equalities, and the compact
cardinality theorem now implemented.

The scope caveat is essential.  This counts integer `b` values for the isolated
cleared numerator lower bound only.  It does not prove that the counted values
are terminal variables satisfying `\tilde t_{s,k}=0`, that they are feasible
exponent chains, or that they imply Lemma 5's pole-order count.

Controller verification ran
`lake env lean DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`.
