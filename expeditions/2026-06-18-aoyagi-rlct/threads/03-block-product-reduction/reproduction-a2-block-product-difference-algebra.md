# A2 block product-difference algebra reproduction

Date: 2026-06-23.

Source context: Aoyagi 2023 preprint, p. 13 discussion after Theorem 3, as
tracked in `regular-suspension-plan.md`.  This reproduction uses only the
elementary block algebra following the already-formalized triangular endpoint
form; it does not use the quiver paper or quiver Lean development.

## Setup

Let the top/source block have row and column index `ι`, let the left residual
row index be `μ`, and let the right residual column index be `ν`.  Work over a
commutative ring.  Let

```text
F2 : Matrix ι ν R,
F3 : Matrix μ ι R,
T  : Matrix (ι ⊕ μ) (ι ⊕ ν) R,
Ctop : Matrix ι ι R,
D : Matrix μ ν R.
```

Define the triangular endpoint multipliers and the rank-`r` model block by

```text
L(F3) = fromBlocks 1 0 F3 1,
R(F2) = fromBlocks 1 F2 0 1,
T0    = fromBlocks 1 0 0 0.
```

Assume the endpoint triangular block form

```text
L(F3) * T * R(F2) = fromBlocks Ctop 0 0 D.
```

## Calculation

By distributivity,

```text
L(F3) * (T - T0) * R(F2)
  = L(F3) * T * R(F2) - L(F3) * T0 * R(F2).
```

The second term is a direct block multiplication:

```text
L(F3) * T0
  = fromBlocks 1 0 F3 1 * fromBlocks 1 0 0 0
  = fromBlocks 1 0 F3 0,
```

and therefore

```text
L(F3) * T0 * R(F2)
  = fromBlocks 1 0 F3 0 * fromBlocks 1 F2 0 1
  = fromBlocks 1 F2 F3 (F3 * F2).
```

Substituting the assumed triangular form gives

```text
L(F3) * (T - T0) * R(F2)
  = fromBlocks Ctop 0 0 D
      - fromBlocks 1 F2 F3 (F3 * F2)
  = fromBlocks (Ctop - 1) (-F2) (-F3) (D - F3 * F2).
```

The dimensions force the lower-right correction to be `F3 * F2`, of type
`Matrix μ ν R`; the opposite product is not well-typed in general.

## Independent Check

An xhigh pen-and-paper check by `Lorentz` confirmed the same identity and sign
pattern.  The check stressed that this is pointwise block-matrix algebra only:
it uses the displayed triangular block form and distributivity, and gives no
RLCT, additivity, or pole-order conclusion.

## Boundary

This slice proves only the algebraic product-difference identity.  It does not
prove Aoyagi Lemma 1, full Theorem 3 from source hypotheses, analytic generator
transport, regular-suspension additivity, normal crossings, pole order, or
RLCT.  The lower-right block `D` should be read in Lean as the deterministic
residual product already exposed by the endpoint wrapper, not as an unproved
raw product of original lower-right edge blocks.
