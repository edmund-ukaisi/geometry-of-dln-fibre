# Reproduction - A2 with-following rank-cut original-prior local loss with finBasis and volume

Date: 2026-07-07.

Status: proposed Lean wrapper.

## Claim

The latest rank-cut original-prior local-loss endpoint still asks the caller to
supply finite endpoint dimensions and bases:

```text
d : Fin 3 -> Nat,
b : forall j, Basis (Fin (d j)) R (reverseVertex W2 j).
```

This is not mathematical content.  The theorem already assumes

```text
forall j, FiniteDimensional R (W2 j).
```

Therefore the endpoint bases can be fixed to Lean's `Module.finBasis` choice:

```text
d j = Module.finrank R (reverseVertex W2 j),
b j = Module.finBasis R (reverseVertex W2 j).
```

Here "fixed" means Lean's chosen `Module.finBasis`, not a mathematically
canonical basis of an abstract vector space.

The resulting finite-integral statement has the same original-prior measure,
same rank-cut source, same residual zero-locus nullity hypothesis, same
source-data and fixed-base centering hypotheses, same regular Haar input, and
same product-zero prior-density continuity/positivity hypotheses.  It only
removes the need for a caller to thread arbitrary endpoint bases through the
local `lossDLN` matrix expression.

A second specialization can then fix the regular-coordinate Haar measure to

```text
volume : Measure (EuclideanSpace R rhoReg).
```

This is safe because the preceding statement is universal over all regular
Haar measures.  It only instantiates that universal quantifier with the
standard `volume` measure on `EuclideanSpace R rhoReg` and Lean's finite
dimensional additive-Haar instance for that volume.

## Composition

Start from

```text
exists_open_radius_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_source_base_of_continuousAt_pos_priorDensity_product_zero
```

and instantiate its endpoint-basis continuation with

```text
fun j => Module.finBasis R (reverseVertex W2 j).
```

Lean infers the implicit dimension function as

```text
fun j => Module.finrank R (reverseVertex W2 j).
```

The final target matrix becomes

```text
toMatrix (Module.finBasis R (reverseVertex W2 0))
  (Module.finBasis R (reverseVertex W2 (last 2)))
  (chainMap ...)
```

and the variable matrix tuple is formed by

```text
chainMapMatrixTuple
  (fun j => Module.finBasis R (reverseVertex W2 j))
  (fun p => CedgeProd(E,u) p)
```

## Nonclaims

- No residual zero-locus-nullity proof.
- No proof that `sourceChart z0` is the fixed reverse-edge base family.
- No source-data construction.
- No proof of product-zero continuity from continuity at `sourceChart z0`.
- No statistical prior identification or transport through p.13 coordinates.
- No determinant/raw Haar transport.
- No source-rank or analytic atlas coverage.
- No normal-crossing construction, pole-order count, or RLCT extraction.

## Regular Haar Note

The regular Haar specialization uses Lean's standard additive-Haar instance for

```text
volume : Measure (EuclideanSpace R rhoReg).
```

This avoids identifying that `EuclideanSpace` volume definitionally with the
product volume on `rhoReg -> R`; the theorem only needs the additive-Haar
property.

Raw Haar is not specialized.  The raw endpoint Haar measure belongs to the
p.13 source-measure comparison and determinant-normalization layer; fixing it
would be a separate transport/normalization claim.

## Additional Nonclaims

- No statement that `Module.finBasis` is mathematically canonical.
- No statement that the original prior is expressed in `Module.finBasis`
  coordinates; the prior measure still uses `paperEndpointFixedBaseFinBasis`.
- No raw Haar specialization.
