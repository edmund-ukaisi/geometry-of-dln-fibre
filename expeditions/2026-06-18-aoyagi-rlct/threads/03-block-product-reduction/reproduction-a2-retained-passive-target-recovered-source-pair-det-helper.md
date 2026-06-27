# Reproduction - A2 target-recovered source pair and product determinant helper

Date: 2026-06-27.

## Scope

This note records a small infrastructure slice for the retained-passive
target-side normalizer.  It is independent of the quiver paper and uses only
the local retained-passive coordinate algebra already formalised for Aoyagi's
product-reduction chart.

The goal is not to construct the full determinant-one target normalizer.  The
slice only packages two reusable facts:

1. after forming the target-side normalized `(F2,C)` edge pair, applying the
   point-specialized formal edge-pair inverse recovers the source `(F2,C)`
   tangent on actual raw-order derivative targets;
2. the determinant of a product linear equivalence is the product of the
   determinants of the two factors.

## Pen-and-paper calculation

Let `D_z raw(v)` be the raw-order Frechet derivative target tuple and let

```text
U_FC(w) = retainedPassiveTargetEdgePairShearAt(z,w).
```

The already-proved target edge-pair bridge says

```text
U_FC(D_z raw(v)) =
  (formal(z)(v).F2, formal(z)(v).C).
```

The point-specialized formal `(F2,C)` map is a linear equivalence

```text
E_z : (source F2, source C) ~= (formal F2, formal C),
```

and the already-proved inverse recovery says

```text
E_z^{-1}(formal(z)(v).F2, formal(z)(v).C) =
  (v.F2, v.C).
```

Therefore the target-side recovered source pair

```text
R_FC(z,w) := E_z^{-1}(U_FC(w))
```

satisfies

```text
R_FC(z,D_z raw(v)) = (v.F2, v.C).
```

The `C` projection is just the second component:

```text
R_C(z,w,q) := R_FC(z,w).C(q),
R_C(z,D_z raw(v),q) = v.C(q).
```

This is the input needed by the future target-only lower-left recurrence,
where the source-direction term `v.C(r)` must be replaced by a function of an
arbitrary target tuple `w`.

For determinants, if `eM : M ~= M` and `eN : N ~= N`, then
`eM.prodCongr eN` is represented by the product map on `M x N`, hence

```text
det(eM.prodCongr eN) = det(eM) det(eN).
```

This is a direct specialization of the existing `linearMap_det_prodMap_eq_mul`
lemma and is intended to remove repeated boilerplate in staged product lifts of
target-side shears.

## Checks

The focused builds passed:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb \
  DLNFibre.DLN.Aoyagi.MatrixLinearDeterminant

env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb \
  DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
```

The full build also passed with only pre-existing warning noise:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
```

The standard hygiene checks passed:

```text
scripts/sorries
git diff --check
rg -n "sorry|#exit|native_decide|axiom" \
  lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean \
  lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```
