# Statement Card - A2 Euclidean coordinate square-sum base integrability

Date: 2026-06-25.

## Claim

Let `eta` be finite and nonempty, and let
`x : EuclideanSpace ℝ eta`.  Put

```text
S(x) = aoyagiCoordinateSquareSum (fun i : eta => x i).
```

For any additive Haar measure `mu` on `EuclideanSpace ℝ eta`, if

```text
R > 0,
t >= 0,
2*t < card eta,
```

then

```text
∫ x in ball(0,R), ENNReal.ofReal(S(x)^(-t)) dmu < infinity.
```

For any nonatomic measure, `S(x)>0` almost everywhere.

Combining these two facts with the variable-base square-model product estimate
gives the finite product integral for

```text
(S(x)+||u||^2)^(-(t+finrank_R(E)/2))
```

over

```text
ball_base(0,Rbase) x ball_fiber(0,Rfiber).
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

Theorems:

```text
DLNFibre.DLN.Aoyagi.aoyagiEuclideanCoordinateSquareSum_pos_of_ne_zero
DLNFibre.DLN.Aoyagi.ae_aoyagiEuclideanCoordinateSquareSum_pos
DLNFibre.DLN.Aoyagi.ae_aoyagiEuclideanCoordinateSquareSum_pos_restrict
DLNFibre.DLN.Aoyagi.lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_indicator_ball_lt_top
DLNFibre.DLN.Aoyagi.lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_restrict_ball_lt_top
DLNFibre.DLN.Aoyagi.lintegral_ofReal_euclideanCoordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
```

## Proof Ingredients

- Aoyagi coordinate square-sum:
  `aoyagiCoordinateSquareSum`;
- Euclidean norm-square identity:
  `EuclideanSpace.real_norm_sq_eq`;
- finite dimension identity:
  `finrank_euclideanSpace`;
- existing radial theorem:
  `lintegral_ofReal_norm_sq_add_rpow_neg_indicator_ball_lt_top`;
- restricted-measure lower-integral rewrite:
  `lintegral_indicator`.

## Nonclaims

- No theorem for Aoyagi's actual residual product map `D = prod_s C^(s)`.
- No local equivalence between the residual product map and free Euclidean
  coordinates.
- No endpoint theorem, divergent-side theorem, or threshold equality.
- No bounded-density/prior theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No Aoyagi Lemma 1, Aoyagi Theorem 4, or regular-coordinate additivity.
- No normal-crossing construction, pole order, or RLCT.
