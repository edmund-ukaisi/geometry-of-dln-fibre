# Review - A2 Euclidean coordinate square-sum base integrability

Date: 2026-06-25.

Reviewer: xhigh `Huygens the 4th`.

Status: passed with no findings.

## Scope

Reviewed the Euclidean coordinate square-sum base-integrability slice in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

especially:

```text
aoyagiEuclideanCoordinateSquareSum_pos_of_ne_zero
ae_aoyagiEuclideanCoordinateSquareSum_pos
ae_aoyagiEuclideanCoordinateSquareSum_pos_restrict
lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_indicator_ball_lt_top
lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_restrict_ball_lt_top
lintegral_ofReal_euclideanCoordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
```

and the accompanying reproduction and statement card.

## Findings

No high-, medium-, or low-severity findings.

## Soundness Notes

The Lean additions match their stated scope: Euclidean coordinate square-sum
positivity, local base integrability under `0 <= t` and `2*t < card eta`, and
the product corollary only for free Euclidean base coordinates.

The documentation explicitly avoids the dangerous overclaim: no theorem for
Aoyagi's actual residual product map `D = prod_s C^(s)`, no local equivalence
with free Euclidean coordinates, and no use of Aoyagi Lemma 1, Aoyagi Theorem 4,
regular-coordinate additivity, quiver-paper input, pole order, or RLCT
extraction.

## Verification

The reviewer ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
git diff --check
```

Both passed.  The controller also runs the expedition build gates before
committing this slice.
