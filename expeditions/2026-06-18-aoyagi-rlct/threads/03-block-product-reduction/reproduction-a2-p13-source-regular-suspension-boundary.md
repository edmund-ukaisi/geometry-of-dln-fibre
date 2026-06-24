# Reproduction - A2 p.13 source regular-suspension boundary

Date: 2026-06-24.

Status: pen-and-paper reproduced; regular-suspension RLCT step remains open.

## Source Anchor

Source: Aoyagi 2023 preprint,
`paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf`,
printed pp. 10-14.  The local VM has no `pdftotext`; the pages were checked
from Ghostscript-rendered page images.

On p. 10, Lemma 2 proves the one-block Schur reduction.  For

```text
A = [ A1  A2
      A3  A4 ],
```

with `A1` an invertible `r x r` block, Aoyagi writes triangular factors

```text
Q1 = [ Er   0 ],       Q2 = [ Er   F2 ],
     [ F3   I ]            [ 0    I  ],
```

and the proof identifies

```text
F2 = - A1^{-1} A2,
F3 = - A3 A1^{-1},
C4 = - A3 A1^{-1} A2 + A4,
Q1 A Q2 = [ A1  0
            0   C4 ].
```

On p. 11, Theorem 3 states that near the normalized target product

```text
prod_s A*^(s) = [ Er  0
                  0   0 ],
```

there are regular triangular matrices

```text
P1 = [ Er  0 ],       P2 = [ Er  F2 ],
     [ F3  I ]            [ 0   I  ],
```

such that

```text
P1 (prod_s A^(s)) P2
  = [ C1  0
      0   prod_s C^(s) ].
```

On pp. 12-13, the induction step assumes

```text
Q1' (prod_{s=1}^S A^(s)) Q2'
  = [ C1'  0
      0    prod_{s=1}^S C^(s) ],
```

with `C1'` regular, then writes

```text
A'^(S+1) = (Q2')^{-1} A^(S+1)
         = [ A1'  A2'
             A3'  A4' ],
C^(S+1) = - A3' (A1')^{-1} A2' + A4'.
```

After another Schur reduction, the new block diagonal form is

```text
Q1'' Q1' (prod_{s=1}^S A^(s)) A^(S+1) Q2''
  = [ C1' A1'  0
      0         prod_{s=1}^{S+1} C^(s) ].
```

## Literal p.13 Product-Difference Block

Immediately after Theorem 3, p. 13 applies the triangular factors to the
target-centered product and displays

```text
P1 (prod_s A^(s) - [ Er 0; 0 0 ]) P2
  =
[ C1 - Er                -F2
  -F3        prod_s C^(s) - F3 F2 ].
```

Thus the full target-centered generator family is represented, after
triangular multiplication, by the entries of

```text
X = C1 - Er,
F2,
F3,
D - F3 F2,
```

where

```text
D = prod_s C^(s).
```

The reduced residual generator family is the entries of `D`, not the displayed
lower-right block `D - F3 F2`.  The already-proved algebraic ideal and
finite square-sum comparisons use this distinction:

```text
<X, F2, F3, D - F3 F2> = <X, F2, F3, D>
```

as a matrix-entry ideal over a commutative ring, and over real finite
coordinates the literal square-sum and the cleaned square-sum are locally
mutually bounded by a constant factor once the `F2` and `F3` square-sums are
small.

## Source RLCT Shift Assertion

Still on p. 13, Aoyagi writes the learning-coefficient decomposition

```text
lambda_w*( < prod_s A^(s) - prod_s A*^(s) > )
  =
  (r^2 + r(H^(1) + H^(L+1) - 2r)) / 2
    + lambda_w*( < prod_s C^(s) > )
```

and equivalently

```text
  =
  (-r^2 + r(H^(1) + H^(L+1))) / 2
    + lambda_w*( < prod_s C^(s) > ).
```

The displayed regular count is

```text
r^2 + r(H^(L+1)-r) + (H^(1)-r)r
  = -r^2 + r(H^(1)+H^(L+1)).
```

This is the expected contribution of the regular blocks `C1-Er`, `F2`, and
`F3`.  The pages do not supply the analytic proof that these blocks form
genuine regular local coordinates, compute the analytic Jacobian/prior shift,
or construct a full normal-crossing chart from a reduced one.

The finite Lean operation `jacobianPriorLossShift` records the exponent-array
effect such a regular-suspension construction would have.  It does not prove
that the p. 13 full loss is represented by the shifted reduced certificate.

## p.14 Residual Reduction

At the bottom of p. 13, Aoyagi defines

```text
M(s) = H^(s) - r,  for s = 1,...,L+1.
```

On p. 14, after invoking Theorem 4, the paper says it can set `r(s)=r` for
`s=1,...,L` without loss of generality, defines

```text
C^(s) = (c_ij^(s)),
1 <= i <= M(s),   1 <= j <= M(s+1),
```

and turns to the log canonical threshold of

```text
|| prod_s C^(s) ||^2.
```

This `r(s)=r` reduction is not a consequence of Theorem 3 alone in the printed
argument; it depends on the separate Theorem 4 invocation.

## Lean-Ready Boundary

The regular-suspension RLCT equality is not Lean-ready under the expedition's
current citation policy.  The next elementary Lean-ready source-side wrapper is
only this:

from real fixed-base rank data and a continuous reversed-edge family based at
`B`, choose the total-kernel complement and the existing
`PaperEndpointFixedBaseRegularCoordinateSourceData`; then, in the
`nhdsWithin` filter of the source-rank stratum, the literal p. 13
product-difference square-sum and the cleaned square-sum are mutually bounded
by factor `2`.

This wrapper consumes already-proved facts:

```text
exists_paperEndpointFixedBaseRegularCoordinateSourceData_of_rank_eq
PaperEndpointFixedBaseRegularCoordinateSourceData.
  literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source
```

and proves no new analytic regular-suspension fact.

## Nonclaims

- No proof that `C1-Er`, `F2`, and `F3` are analytic local coordinates.
- No local analytic inverse or source chart coverage theorem.
- No analytic ideal-germ transport from the literal full product-difference
  generators to a product of regular variables and the reduced residual loss.
- No Jacobian determinant or prior-density calculation for the p. 13
  coordinate change.
- No construction of a full normal-crossing certificate `Cfull` from a reduced
  certificate `Cred`.
- No proof of the p. 13 RLCT equality.
- No use of Theorem 4 as a cited boundary for the residual `r(s)=r` reduction.

## Kill Conditions

- Treating `Cred.exponentData.jacobianPriorLossShift c` as the actual full
  certificate.
- Stating `PaperEndpointFixedBaseRegularCoordinateSourceData -> exists Cfull`
  without concrete analytic chart, coverage, transport, and Jacobian fields.
- Replacing analytic regular-coordinate obligations by predicates with `True`
  fields.
- Reading the p. 13 displayed lower-right block as `prod_s C^(s)` instead of
  `prod_s C^(s) - F3 F2`.
- Treating the p. 14 `r(s)=r` reduction as part of Theorem 3.
