# A2 retained-passive canonical residual measurability handoff

Status: Lean proved; focused/full builds and local gates passed; xhigh review
passed.

## Claim

For the canonical retained-passive p.13 source, the residual positive-set
measurability hypothesis is finite Borel bookkeeping and should not remain a
separate analytic input.

With

```text
EFam = forall p : Fin (M+1),
  reverseVertex W p.castSucc ->L[R] reverseVertex W p.succ
Cedge = id : EFam -> EFam,
```

the set

```text
{x : EFam |
  0 < aoyagiCoordinateSquareSum
    (paperEndpointFixedBaseResidualBlockCoordinateMap W B U0 hU0 Cedge x)}
```

is measurable.

## Reproduction

The p.13 residual block coordinate is the `D` field of the fixed-base suffix
state attached to the edge matrix family.  For a general measurable source
space, the existing bookkeeping theorem says:

```text
Measurable edgeMatrix(Cedge)
  -> Measurable residualBlockCoordinateMap(Cedge).
```

In the canonical source, `Cedge` is the identity on `EFam`.  The edge-matrix
map

```text
x |-> paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U0 hU0
  (fun p => (x p : reverseVertex W p.castSucc ->_R reverseVertex W p.succ))
```

is continuous because it is the fixed-basis matrix coordinate map applied to a
globally continuous edge family.  The identity map on `EFam` is continuous, so
the retained-passive local-source continuity API gives continuity of the
edge-matrix map, hence measurability.

Composing the measurable edge-matrix map with the finite suffix recursion gives
measurability of

```text
x |-> paperEndpointFixedBaseResidualBlockCoordinateMap W B U0 hU0 id x.
```

The coordinate square-sum is a finite polynomial expression in those residual
coordinates, hence measurable.  The target set is the preimage of the open
interval `(0, infinity)` under this measurable real-valued square-sum.  It is
therefore measurable.

## Composition

The generic canonical residual handoff currently takes three residual-side
inputs:

```text
source-side residual positive-set measurability,
chart-side residual positivity a.e.,
chart-side finite residual negative-power integral.
```

This checkpoint discharges only the first input for `Cedge = id`.  The new
front-end residual handoff should take only the chart-side a.e. positivity and
chart-side finite integral, then call the existing canonical residual handoff
with the proved source-side measurability.

The finite-integral front ends can then receive analogous `of_chartSide`
wrappers: they still take the chart-side positivity, chart-side finite
integral, local loss lower bound, and density hypotheses, but no longer take
source-side residual positive-set measurability.

## Lean result

The Lean names are:

```text
measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_id
residualSourceHypotheses_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_of_chartSide
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_of_chartSide
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_continuousAt_pos_density_of_chartSide
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

The first theorem proves source-side residual positive-set measurability for
the canonical identity edge-family source.  The next three are front ends for
the canonical product-density residual handoff, fixed-radius finite-integral
handoff, and radius-shrinking continuous-density finite-integral handoff.  They
remove only the source-side residual positive-set measurability argument.

Verification run:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
rg -n "sorry|axiom|native_decide|#exit|admit" lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

Both builds passed.  The full build produced only pre-existing warning noise.
`scripts/sorries` reported zero forbidden declarations, `git diff --check`
was clean, and the touched-file forbidden-marker search returned no matches.

## Boundary

This checkpoint proves no zero-locus nullity and no residual integrability.
It does not prove chart-side a.e. residual positivity.  It does not prove a
monomial residual lower bound, construct a signed-box source-density, transport
an original prior, produce normal crossings, compute pole order, or extract an
RLCT.

## Kill conditions

- The proof uses continuity or measurability of an original-prior/source
  density rather than only the finite fixed-base edge-matrix coordinates.
- The wrapper silently removes chart-side residual positivity or finite
  negative-power integrability.
- The result is stated for arbitrary `Cedge`; the proof only covers the
  canonical identity source family.
- The theorem is used as evidence for zero-set nullity, normal crossings,
  pole order, or RLCT.
