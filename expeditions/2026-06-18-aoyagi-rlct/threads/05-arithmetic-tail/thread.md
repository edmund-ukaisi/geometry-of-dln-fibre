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

## 2026-06-20 Lean Lemma 3 equality count

Reproduction:
`reproduction-lemma3-equality-count-a5.md`.
Statement card:
`statement-card-a5-lemma3-equality-count.md`.
Review artifact:
`review-lemma3-equality-count-a5.md`.

Lean now defines the finite equality set
`aoyagiLemma3AMinimizerSet ell a` as the integer source interval
`0 <= b <= ell-1` filtered by equality with the isolated lower bound.  It proves
the set is `{0}` at `a=0`, `{ell-1}` at `a=ell`, and `{a-1,a}` in the strict
interior `0<a<ell`.  The combined cardinality theorem is

```text
card = 1 + if 0 < a and a < ell then 1 else 0
```

under `1 <= ell` and `0 <= a <= ell`.

This is not Lemma 5's pole-order count.  It counts only integer `b` values for
the isolated Lemma 3 numerator equality, not terminal variables, exponent-chain
feasibility, chart-family coordinates, or RLCT data.

## 2026-06-20 Lean Lemma 5 interval-excess arithmetic

Reproduction:
`reproduction-lemma5-interval-excess-a5.md`.
Statement card:
`statement-card-a5-lemma5-interval-excess.md`.
Review artifact:
`review-lemma5-interval-excess-a5.md`.

Lean now proves the elementary interval-size sum used in Aoyagi's Lemma 5 in
`lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`.  The closed excess
formula is

```text
min(j, ell-j, a, ell-a),
```

encoded as nested `min`s.  It is identified with fibers of the rectangle
`range a x range (ell-a)` under the level map `(p,q) |-> p+q+1`, and summing
these fibers proves

```text
1 + sum_{j=1}^{ell-1} (intervalSize(ell,a,j)-1) = a(ell-a)+1
```

under `1 <= ell` and `a <= ell`.

This is still not Lemma 5.  It proves only finite interval-excess arithmetic,
not the chart-family constructions, admissibility, coverage, pole-order
interpretation, normal crossings, or RLCT extraction.

## 2026-06-20 Lean Lemma 4 two-value count

Reproduction:
`reproduction-lemma4-two-value-count-a5.md`.
Statement card:
`statement-card-a5-lemma4-two-value-count.md`.
Review artifact:
`review-lemma4-two-value-count-a5.md`.

Lean now proves the finite count used in Aoyagi's Lemma 4 in
`lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`.  If an `ell`-indexed
integer family takes only values `M-1` and `M`, and its sum is

```text
ell*(M-1)+a,
```

then exactly `a` entries are `M` and exactly `ell-a` entries are `M-1`.
The theorem also records that these hypotheses force `a <= ell`.

This is only finite count arithmetic.  The source bridge from `H_ell=0` to the
sum identity, the `H_0` convention for `F_1`, vector inequalities,
correspondence to `lambda`, Lemma 5, pole order, normal crossings, and RLCT
extraction remain open.
