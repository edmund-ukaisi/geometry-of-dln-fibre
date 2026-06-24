# Reproduction - A2 regular/residual ideal split

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi PDF p. 13 separates the post-product-reduction variables into the
regular block families

```text
C1 - Er,   F2,   F3
```

and a residual block `D`.  The regular families contribute the finite regular
variable count; the residual block is where the lower-dimensional normal
crossing problem remains.

## Calculation

For matrices

```text
X, F2, F3, D
```

define the regular block-entry ideal by

```text
Ireg(X,F2,F3) = <entries X> + <entries F2> + <entries F3>.
```

The existing four-block ideal is

```text
Ifour(X,F2,F3,D)
  = <entries X> + <entries F2> + <entries F3> + <entries D>.
```

Thus

```text
Ifour(X,F2,F3,D) = Ireg(X,F2,F3) + <entries D>.
```

No new algebra is hidden here: it is only regrouping the four entry-generator
families.  In Lean this is made definitional by defining
`fourMatrixEntryIdeal` as

```text
regularBlockEntryIdeal X F2 F3 ⊔ matrixEntryIdeal D.
```

The product-difference cleanup already proves the unsplit equality

```text
matrixEntryIdeal(productDifference)
  = fourMatrixEntryIdeal (Ctop - 1) F2 F3 D.
```

Composing with the definitional split gives

```text
matrixEntryIdeal(productDifference)
  = regularBlockEntryIdeal (Ctop - 1) F2 F3 ⊔ matrixEntryIdeal D.
```

For the canonical fixed-base suffix-state fields the signs and names are

```text
X  = S.Ctop - 1,
F2 = -S.B,
F3 = lowerLeftBlock S.L,
D  = S.D.
```

The residual block `S.D` is intentionally not a regular coordinate.

## Nonclaims

- No analytic germ-ideal transport.
- No regular-suspension chart construction.
- No chart coverage or Jacobian compatibility.
- No normal-crossing production, pole-order theorem, or RLCT theorem.
- No claim that `S.D` is a raw untransformed product; it is the deterministic
  residual block produced by the suffix-state/product-reduction construction.
