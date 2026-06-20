# Review - A5 Lemma 4 two-value count

Reviewed objects:

- `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`
- `reproduction-lemma4-two-value-count-a5.md`
- `statement-card-a5-lemma4-two-value-count.md`

Verdict: no blocking arithmetic or scope issue found for the isolated
two-value count sub-slice.

Independent xhigh pen-and-paper checker `Hume the 5th` verified that if every
`F_j` is either `M-1` or `M`, and

```text
sum_j F_j = ell*(M-1)+a,
```

then

```text
#{j : F_j = M} = a,
#{j : F_j = M-1} = ell-a.
```

The checker emphasized that the source bridge from `H_ell=0` to the sum
identity is separate and is not proved in this sub-slice.

Independent xhigh Lean scout `Chandrasekhar the 5th` recommended the
integer-valued theorem now implemented, rather than a natural-number `M-1`
form that would need extra nonzero hypotheses to avoid predecessor truncation.

This must not be presented as Lemma 4 itself.  It proves only finite counting
from two-value and sum hypotheses.  It does not prove the `H_0` convention,
the `H_ell=0` sum bridge, vector admissibility, Lemma 4's correspondence to
`lambda`, Lemma 5, pole order, normal crossings, or RLCT extraction.

Controller verification ran
`lake env lean DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`.
