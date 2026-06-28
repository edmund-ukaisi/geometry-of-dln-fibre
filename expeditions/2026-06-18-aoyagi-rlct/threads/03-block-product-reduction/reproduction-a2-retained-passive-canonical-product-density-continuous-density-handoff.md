# A2 retained-passive canonical product-density continuous-density handoff

Status: Lean proved; focused/full builds and local gates passed; xhigh review
passed.

## Claim

The canonical retained-passive product-density finite-integral handoff can
replace its local density nonnegativity and local density upper-bound
hypotheses by the standard local condition that the transported density factor
is continuous and strictly positive at the chart center.

This is a density-bound hardening of the previous checkpoint.  It does not
prove the chart-side residual hypotheses or the local loss lower bound.

## Setup

Use the canonical retained-passive source data from the previous checkpoint:

```text
EFam = forall p : Fin (M+1),
  reverseVertex W p.castSucc ->L[R] reverseVertex W p.succ
base = fun p => LinearMap.toContinuousLinearMap (reverseEdge W B p)
Cedge = id : EFam -> EFam
mu = Measure.map sourceChart (m.restrict T)
nuChart = (m.restrict S).withDensity (fun z => ofReal productDensity(z)).
```

Let `rhoReg` be the p.13 regular-coordinate Euclidean index and let

```text
density : EFam x EuclideanSpace R rhoReg -> R
```

be the remaining transported density factor in the final product integral.
Assume

```text
ContinuousAt density (base, 0),
0 < density(base, 0),
0 < Rmax.
```

The generic local-measure helper

```text
exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
```

applied to the retained-passive local source gives `R` and `C` with

```text
0 < R,  R <= Rmax,  0 <= C,
```

and, eventually on `nhdsWithin base localSource`, uniformly for
`u in ball(0,R)`,

```text
0 <= density(x,u),
density(x,u) <= C.
```

The loss lower bound hypothesis is assumed at radius `Rmax`.  Since
`R <= Rmax`, the same lower bound holds at radius `R` by ball inclusion.

## Composition

The previous theorem

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet
```

takes:

```text
R, C,
chart-side residual positive-set measurability,
chart-side residual positivity,
chart-side finite residual integral,
local loss lower bound at R,
local density nonnegativity at R,
local density upper bound at R.
```

Substituting the `R,C` and local density bounds from continuity gives the
continuous-density handoff:

```text
exists R C U,
  0 < R and R <= Rmax and 0 <= C and U open and base in U
  and the p.13 finite integral over
    (mu.restrict (U inter sourceStratum)).prod nuReg
  is finite.
```

## Lean result

The Lean theorem is:

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_continuousAt_pos_density
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

The proof calls
`exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos`
with `s := localSource`, `Rmax := Rmax`, and the regular Euclidean coordinate
space.  It then restricts the loss lower bound from `Rmax` to the output
radius `R` using `Metric.ball_subset_ball hRle`, and delegates to the previous
canonical product-density finite-integral theorem.

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

This checkpoint removes only two local density-bound hypotheses.  It keeps the
chart-side residual positive-set measurability, chart-side residual positivity,
chart-side finite residual integral, and local loss lower bound explicit.  It
does not construct an original source prior, identify a selected-entry
signed-box density, prove a monomial residual lower bound, produce normal
crossings, compute pole order, or extract an RLCT.

The scouts after VM recovery also identified the next honest cleanup boundary:
the source-side residual positive-set measurability for the canonical identity
edge-family map appears dischargeable from existing measurability APIs, but
chart-side a.e. residual positivity and finite negative-power integrability
still require genuine zero-locus or normal-crossing input.  The present theorem
does not hide either analytic hypothesis.

## Kill conditions

- The density-bounds helper is applied to the wrong source set rather than the
  retained-passive local source.
- The loss lower bound is not restricted from `Rmax` to the smaller output
  radius `R`.
- The theorem hides residual integrability or residual positivity instead of
  keeping the chart-side hypotheses explicit.
- The statement claims a Jacobian/prior density construction rather than only
  bounding a supplied continuous positive density factor.
