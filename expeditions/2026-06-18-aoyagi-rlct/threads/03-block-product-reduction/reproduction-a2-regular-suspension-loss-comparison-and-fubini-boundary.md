# Reproduction - A2 regular-suspension loss comparison and Fubini boundary

Date: 2026-06-24.

Status: pen-and-paper reproduced; finite square-sum comparison partially
formalised in Lean.

## Source Anchor

Aoyagi PDF p. 13 gives the literal product-difference block

```text
P1 (prod_s A^(s) - [E_r 0; 0 0]) P2
  =
[ C1 - E_r              -F2
  -F3        prod_s C^(s) - F3 F2 ].
```

The regular blocks are

```text
C1 - E_r,   F2,   F3,
```

and the reduced residual block is

```text
D = prod_s C^(s).
```

The displayed lower-right block is not `D`; it is `D - F3 F2`.

## Literal and Cleaned Square-Sums

For finite real matrices

```text
X  : iota x iota,
F2 : iota x nu,
F3 : mu x iota,
D  : mu x nu,
```

write

```text
A = ||X||_F^2 + ||F2||_F^2 + ||F3||_F^2,
B = ||D||_F^2,
E = ||D - F3 F2||_F^2,
P = ||F3 F2||_F^2.
```

Then

```text
L_clean = A + B,
L_lit   = A + E.
```

The elementary pointwise estimates

```text
||D - Pmat||_F^2 <= 2 ||D||_F^2 + 2 ||Pmat||_F^2,
||D||_F^2        <= 2 ||D - Pmat||_F^2 + 2 ||Pmat||_F^2
```

give

```text
E <= 2B + 2P,
B <= 2E + 2P.
```

## Product-Correction Bound

For `Pmat = F3 F2`, row-column Cauchy-Schwarz gives

```text
||F3 F2||_F^2 <= ||F3||_F^2 ||F2||_F^2.
```

If

```text
||F2||_F^2 + ||F3||_F^2 <= 1,
```

then

```text
4 ||F3||_F^2 ||F2||_F^2
  <= (||F2||_F^2 + ||F3||_F^2)^2
  <= ||F2||_F^2 + ||F3||_F^2
  <= A.
```

Thus

```text
4P <= A.
```

Consequently

```text
L_lit = A + E <= A + 2B + 2P <= 2(A+B) = 2 L_clean,
L_clean = A + B <= A + 2E + 2P <= 2(A+E) = 2 L_lit.
```

Equivalently, on the neighborhood where
`||F2||_F^2 + ||F3||_F^2 <= 1`,

```text
(1/2) L_clean <= L_lit <= 2 L_clean.
```

This comparison uses no smallness of `X` or `D`.  In the later source-stratum
setting, centered continuity of the `F2` and `F3` coordinate maps should be
enough to shrink to such a neighborhood; that neighborhood shrink is not
proved in this slice.

## Regular-Variable Fubini Boundary

The separate analytic theorem still needed for the regular-variable shift is:

if `g(y) >= 0` is the reduced residual analytic square-loss germ and

```text
G(u,y) = ||u||^2 + g(y)
```

in `c` genuine regular coordinates `u`, then product-coordinate Fubini plus
polar integration should give

```text
lambda(G) = lambda(g) + c/2,
theta(G)  = theta(g).
```

For Aoyagi p. 13,

```text
c = r^2 + r(H^(L+1)-r) + (H^(1)-r)r
  = -r^2 + r(H^(1)+H^(L+1)).
```

This theorem is not cited as an additional analytic black box in the
expedition.  It must either be proved or absorbed into a constructed full
normal-crossing certificate to which the single allowed
normal-crossing-to-RLCT extraction citation applies.

## Lean Slice

Lean formalises the finite ordered-ring square-sum part:

- coordinatewise `(a - b)^2` and `(a + b)^2` estimates;
- residual/corrected-residual comparison with the product correction term;
- row-column Cauchy-Schwarz for `F3 * F2`;
- `4P <= A` under `squareSum(F2)+squareSum(F3) <= 1`;
- two-sided factor-`2` comparison between the literal and cleaned finite
  coordinate square-sums under that smallness hypothesis.

## Nonclaims

- No analytic coordinate chart or local inverse.
- No proof that centered continuous scalar maps are genuine analytic regular
  coordinates.
- No neighborhood shrink from continuity to `||F2||^2+||F3||^2 <= 1`.
- No Fubini/polar theorem in Lean.
- No chart coverage, Jacobian/prior compatibility, normal crossings, pole
  order, or RLCT extraction.
- No use of ideal equality as an RLCT or loss-comparison theorem.
