# Thread 05 - arithmetic tail

Type: formalisation. Status: blocked.

## Task

Formalise Aoyagi's finite minimisation and pole-order arithmetic once the
exponent vectors are stable.

## Output contract

- Lean definitions for the relevant finite candidate set and exponent ratios.
- Proofs of the minimisation and order-count lemmas.
- Boundary-case tests/examples for small dimension vectors.

## Controller notes

This should be mostly finite arithmetic. If a proof becomes a long brittle
calculation, consider a small exact certificate generator, but Lean remains the
final authority.

## 2026-06-18 check result

Draft reproduction: `reproduction-draft.md`. Independent checker: `Planck`,
saved at `reproduction-check.md`.

Status: not formalisation-ready. The next arithmetic reproduction must split
Lemma 3 endpoint cases, preserve Aoyagi's `\tilde t_{s,k}=0` restriction, prove
feasibility of the floor/ceil minimisers, and reproduce Lemma 5's
chart-family/order-count construction.

## 2026-06-20 Lean Lemma 3 endpoint arithmetic

Reproduction:
`reproduction-lemma3-endpoint-arithmetic-a5.md`.
Statement card:
`statement-card-a5-lemma3-endpoint-arithmetic.md`.
Review artifact:
`review-lemma3-endpoint-arithmetic-a5.md`.

Lean now proves the isolated integer numerator algebra for Aoyagi's Lemma 3 in
`lean/DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`.  The main identity is

```text
A(b) = a ell (ell-a) + ell^2 (b-a)(b-a+1),
```

and the endpoint-corrected minimum theorem says that, under
`1 <= ell` and `0 <= a <= ell`, the least value over integer
`0 <= b <= ell-1` is `a ell (ell-a)`.  This repairs the endpoint issue for
`a=0` and `a=ell`.

The full A5 claim remains blocked.  This sub-slice does not prove the
terminal candidate set, the `\tilde t_{s,k}=0` restriction, feasibility of
minimising exponent chains, Lemma 4, Lemma 5, pole order, normal crossings, or
RLCT extraction.

## 2026-06-20 Lean Lemma 3 equality cases

Reproduction:
`reproduction-lemma3-equality-cases-a5.md`.
Statement card:
`statement-card-a5-lemma3-equality-cases.md`.
Review artifact:
`review-lemma3-equality-cases-a5.md`.

Lean now also proves the exact equality cases for the same isolated integer
numerator.  If `ell != 0`, then

```text
A(b) = a ell (ell-a) iff b = a or b = a-1.
```

After intersecting with the source interval `0 <= b <= ell-1`, equality is
equivalent to

```text
(b = a and a <= ell-1) or (b = a-1 and 1 <= a).
```

Endpoint corollaries name the remaining candidates at `a=0` and `a=ell`.
This is still only integer polynomial arithmetic and source-interval
bookkeeping.  The full A5 claim remains blocked by the terminal candidate set,
the `\tilde t_{s,k}=0` restriction, exponent-chain feasibility, Lemmas 4-5,
pole order, normal crossings, and RLCT extraction.
