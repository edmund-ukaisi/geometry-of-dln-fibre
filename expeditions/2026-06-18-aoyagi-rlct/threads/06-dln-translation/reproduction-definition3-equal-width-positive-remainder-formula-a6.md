# Reproduction - Equal-Width Positive-Remainder Formula Wrapper

Date: 2026-07-02.

Status: controller reproduction; Lean target implemented and awaiting review.

## Source Anchor

Aoyagi Definition 3 and the equal-width example on PDF pp. 8-9 state the
ceiling inequality and residue formula

```text
M - 1 < ((L + 1) M^(1)) / L <= M,
a = (L + 1) M^(1) - (M - 1)L.
```

For a common reduced width `w`, this is reproduced in Lean by the equivalent
positive-remainder form

```text
w = L*q + a,    0 < a <= L
```

where `M = w + q + 1`.  The existing Lean theorem

```text
exists_consecutive_equalWidth_theorem2Formula_of_constant_reducedWidth_decomposition
```

already formalizes the equal-width Theorem 2 finite formula once this
decomposition is supplied.

## Elementary Calculation

For `0 < L` and `0 < w`, choose

```text
q = (w - 1) / L,
a = (w - 1) % L + 1.
```

Since `(w - 1) % L < L`, we have

```text
0 < a <= L.
```

Euclidean division gives

```text
w - 1 = L*q + ((w - 1) % L),
```

so adding `1` gives

```text
w = L*q + a.
```

Thus the explicit equal-width formula package can choose `q,a` automatically
from `L,w` instead of requiring this derived positive-remainder translation as
a caller input.

## Lean Shape

Add in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3CeilData.exists_positiveRemainderDecomposition
AoyagiDefinition3SourceData.exists_consecutive_equalWidth_theorem2Formula_of_constant_reducedWidth_pos
```

The wrapper assumes:

```text
0 < L,
0 < w,
forall s, 1 <= s -> s <= L+1 ->
  aoyagiReducedWidthInt H r s = (w : Int).
```

It returns existential `q,a`, their positive-remainder facts, consecutive
equal-width source data, explicit ceiling data, the selected pair sum, and the
unfolded finite lambda formula already proved by the decomposition theorem.

## Nonclaims

No arbitrary Definition 3 branch selection, no uniqueness theorem for `q,a`,
no branch-independent formula, no finite exponent certificate, no Eq5 payload,
no chart production, no normal crossings, no pole order, and no RLCT
extraction.
