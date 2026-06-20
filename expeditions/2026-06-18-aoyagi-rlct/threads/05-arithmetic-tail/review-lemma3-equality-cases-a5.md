# Review - A5 Lemma 3 equality cases

Reviewed objects:

- `lean/DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`
- `reproduction-lemma3-equality-cases-a5.md`
- `statement-card-a5-lemma3-equality-cases.md`

Verdict: no blocking arithmetic or scope issue found for the isolated
equality-case sub-slice.

Independent xhigh pen-and-paper checker `Epicurus the 5th` verified that the
completed-square identity gives

```text
A(b) = a ell (ell-a)
  iff ell^2 (b-a)(b-a+1) = 0,
```

and, for `ell != 0`, this is equivalent over the integers to

```text
b = a or b = a-1.
```

The same check confirmed the endpoint truncation under
`1 <= ell` and `0 <= b <= ell-1`:

```text
a = 0:        b = 0 only;
0 < a < ell: b = a-1 or b = a;
a = ell:      b = ell-1 only.
```

Independent xhigh Lean scout `Dalton the 5th` inspected
`ArithmeticTail.lean` and recommended the theorem names and proof strategy now
implemented, including the nonzero `ell` hypothesis and the source-interval
bookkeeping theorem.

The checker emphasized that this must not be presented as Aoyagi's full
Lemma 3.  It proves only equality in the isolated integer numerator lower
bound and interval truncation of the two algebraic candidates.  It does not
address `\tilde t_{s,k}=0`, exponent-chain feasibility, Lemma 4, Lemma 5,
chart coverage, normal crossings, or RLCT extraction.

Controller verification ran
`lake env lean DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`.
