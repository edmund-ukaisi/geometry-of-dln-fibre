# Statement Card - A6 Equal-Width Positive-Remainder Formula Wrapper

Date: 2026-07-02.

## Claim

For the equal-width lane, the positive-remainder decomposition required by the
explicit finite Theorem 2 formula can be constructed automatically from
`0 < L` and `0 < w`.

## Source Status

Aoyagi's equal-width example states the ceiling inequality and residue formula

```text
M - 1 < ((L + 1) M^(1)) / L <= M,
a = (L + 1) M^(1) - (M - 1)L.
```

For a common reduced width `w`, the existing Lean equal-width package
reproduces this by the positive-remainder translation

```text
w = L*q + a,    0 < a <= L.
```

The construction of such `q,a` is elementary Euclidean division applied to
`w-1`; the downstream formula is the already-formalized equal-width finite
formula package from Aoyagi Definition 3/Theorem 2, PDF pp. 8-9.

## Pen-and-paper Reproduction

Reproduction:
`reproduction-definition3-equal-width-positive-remainder-formula-a6.md`.

## Lean Target

File: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

Lean names:

```text
AoyagiDefinition3CeilData.exists_positiveRemainderDecomposition
AoyagiDefinition3SourceData.exists_consecutive_equalWidth_theorem2Formula_of_constant_reducedWidth_pos
```

## Verification So Far

Warning-clean direct elaboration and focused module build passed.

## Nonclaims

No arbitrary Definition 3 branch choice, no branch-independent lambda/order
payload, no finite exponent certificate, no Eq5 payload, no chart production,
no normal crossings, and no analytic pole-order/RLCT extraction.
