# Review - A5 Lemma 3 endpoint arithmetic

Reviewed objects:

- `lean/DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`
- `reproduction-lemma3-endpoint-arithmetic-a5.md`
- `statement-card-a5-lemma3-endpoint-arithmetic.md`

Verdict: no blocking arithmetic or scope issue found for the isolated
Lemma 3 sub-slice.

Independent xhigh checker `Lorentz the 5th` verified the algebraic identity

```text
A(b) = a ell (ell-a) + ell^2 (b-a)(b-a+1)
```

and the endpoint conditions:

```text
a = 0:          witness b = 0;
1 <= a < ell:   witnesses b = a-1 and b = a;
a = ell:        witness b = ell-1.
```

The checker emphasized that this must not be presented as Aoyagi's full
Lemma 3 or as an RLCT/minimum theorem.  It proves only integer polynomial
algebra and the constrained integer minimum over `0 <= b <= ell-1`.  It does
not address `\tilde t_{s,k}=0`, feasibility of exponent chains, Lemma 4,
Lemma 5, chart coverage, normal crossings, or RLCT extraction.

Controller verification ran
`lake env lean DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`.
