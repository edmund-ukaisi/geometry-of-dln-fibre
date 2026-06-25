# Reproduction - A2 p.13 half loss lower bound

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for the finite
source-stratum lower-bound corollary.

## Source Anchor

Aoyagi p. 13 writes the transformed product-difference block, after the
Theorem 3 triangular reduction, as

```text
[[C1 - Er, -F2],
 [-F3, prod_s C^(s) - F3 F2]].
```

The cleaned regular-plus-residual model keeps the regular blocks
`C1-Er`, `F2`, `F3` and separates the residual block

```text
D = prod_s C^(s).
```

The already-landed finite comparison proves on the source-rank `nhdsWithin`
filter that the literal p. 13 square-sum and the cleaned square-sum are
equivalent up to factor `2`.

## Derivation

Write

```text
L_lit   = squareSum(literal p.13 scalar coordinates),
L_reg   = squareSum(regular block scalar coordinates),
L_res   = squareSum(residual block scalar coordinates),
L_clean = L_reg + L_res.
```

The previous source-stratum theorem gives eventually

```text
L_lit <= 2 * L_clean
L_clean <= 2 * L_lit.
```

The second inequality is exactly the lower-bound direction needed for
negative-power estimates.  Since `2>0`,

```text
L_clean <= 2 * L_lit
```

implies

```text
(1/2) * L_clean <= L_lit.
```

This is pure ordered-ring arithmetic.

Now suppose an ambient chart loss is separately known to satisfy, eventually
on the same source-rank filter,

```text
c * L_lit <= loss
```

with `c >= 0`.  Multiplying the half-bound by `c` gives

```text
c * ((1/2) * L_clean) <= c * L_lit.
```

Combining with the supplied ambient comparison gives

```text
(c/2) * (L_reg + L_res) <= loss.
```

The supplied comparison `c * L_lit <= loss` is where determinant-chart
triangular multiplier control for the original DLN loss must enter.  The
finite p. 13 square-sum theorem does not produce it.

The theorem is stated with `c >= 0` because the ordered arithmetic is valid at
that generality.  Downstream negative-power integrability arguments will need
the supplied comparison constant to be strictly positive.

## Lean Shape

Lean proves the half-bound and supplied-loss handoff in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
```

with names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.const_mul_literal_squareSum_eventually_le_loss_to_half_regular_add_residual_squareSum_nhdsWithin_source
exists_paperEndpointFixedBaseRegularCoordinateSourceData_literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source_of_rank_eq
```

## Boundary

This is finite source-side square-sum bookkeeping.  It does not prove:

- comparison of the original DLN loss with `L_lit`;
- analytic coordinate status or chart coverage;
- Jacobian or prior density transport;
- regular-suspension Fubini/polar shift;
- normal crossings, pole order, or RLCT extraction.
