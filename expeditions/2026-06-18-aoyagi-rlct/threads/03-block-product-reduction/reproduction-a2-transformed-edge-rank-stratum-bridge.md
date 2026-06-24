# A2 transformed-edge rank-stratum bridge

Date: 2026-06-24.

Status: checked finite-dimensional rank reproduction for a source-rank boundary
bridge.

## Source Anchor

Aoyagi 2023, Section 5, Lemma 2 and Theorem 3 (PDF pp. 10-13).  In the
product-reduction induction, before applying the one-step Schur complement
calculation to the next layer, the layer matrix is multiplied by the triangular
matrix accumulated from the already-reduced suffix.

## Reproduction

Fix endpoint bases from the base chain `B`, and write a nearby reversed edge in
those fixed bases as `E_p`.  The deterministic suffix recursion stores an
accumulated upper-right block `B_prev`.  The next matrix to which Lemma 2 is
applied is

```text
M_p = [ I  B_prev ] E_p.
      [ 0    I    ]
```

The multiplier

```text
U(B_prev) = [ I  B_prev ]
            [ 0    I    ]
```

is block-unitriangular.  Its determinant is a unit, so left multiplication by
`U(B_prev)` does not change matrix rank:

```text
rank(M_p) = rank(E_p).
```

Therefore the exact rank hypothesis used by the transformed Schur-residual
step,

```text
rank(transformedEdge_p) = r_p,
```

is equivalent, pointwise in `p`, to the fixed-base edge-rank stratum condition

```text
rank(E_p) = r_p.
```

In Lean, `rank(E_p)` is expressed as

```text
Module.finrank K (LinearMap.range (Cedge x p)).
```

The bridge is thus only an equality of finite rank predicates: it identifies
the rank condition used by the recursive transformed-edge calculation with the
already named fixed-base edge-rank stratum.  The larger source-shaped rank
stratum also includes the fixed base product rank and inequalities; those are
not changed by this bridge.

## Lean Target

Lean proves:

```text
paperEndpointFixedBase_transformedEdgeRanks_iff_edgeRankStratum
```

in `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`.

The proof uses the definition

```text
ChartLocalSuffixState.transformedEdge EMat p S
  = [I S.B; 0 I] * EMat p
```

and `Matrix.rank_mul_eq_right_of_isUnit_det` for the determinant-unit
block-unitriangular multiplier.

## Proved

- The recursive transformed-edge rank predicate is equivalent to
  `paperEndpointFixedBaseEdgeRankStratum`.
- The equivalence is pointwise over a fixed endpoint-basis choice and a fixed
  source edge family.
- The accumulated triangular multiplier in `transformedEdge` is rank-preserving.

## Not Claimed

- No exact-rank openness.
- No source-stratum nonemptiness.
- No construction of source charts or transition maps.
- No analytic ideal-germ transport.
- No regular-suspension or RLCT additivity.
- No normal-crossing certificate, pole order, or RLCT extraction.
- No identification of the residual product with a raw product of original
  lower-right edge blocks.

## Kill Conditions

- Do not read the theorem as an ambient-neighborhood result.
- Do not use it to remove the explicit source rank stratum from A2 statements.
- Do not infer any analytic or normal-crossing consequence from this rank
  predicate bridge.
