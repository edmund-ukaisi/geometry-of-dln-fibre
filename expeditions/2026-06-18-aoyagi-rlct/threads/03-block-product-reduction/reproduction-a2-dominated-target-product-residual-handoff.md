# A2 dominated-target product-residual handoff

Status: pen-and-paper reproduction for the next measure handoff.

## Claim

Let `mu` and `nu` be measures on the same source space, let `C : ENNReal`
with `C < infinity`, and assume

```text
nu <= C • mu.
```

If a property `p` holds `mu`-almost everywhere and a nonnegative integrand
`f : alpha -> ENNReal` has finite lower integral over `mu`, then `p` holds
`nu`-almost everywhere and `f` has finite lower integral over `nu`.

The intended Aoyagi specialization takes `p theta` to be positivity of the
p.13 product residual square-sum and `f theta` to be its negative power.

## Calculation

The domination gives absolute continuity:

```text
nu << mu.
```

Indeed Mathlib packages this as
`Measure.absolutelyContinuous_of_le_smul`.  Hence every `mu`-a.e. statement
transfers to `nu`.

For the lower integral, monotonicity gives

```text
lintegral f dnu <= lintegral f d(C • mu).
```

The right-hand side is

```text
C * lintegral f dmu.
```

Since `C < infinity` and `lintegral f dmu < infinity`, their product is
finite.  Therefore `lintegral f dnu < infinity`.

No measurability of `f` is required for this lower-integral comparison.

## Boundary

This proves only a target-measure transfer under an explicit finite-scalar
domination hypothesis.  It does not prove that any concrete Aoyagi source
measure, coordinate source measure, Jacobian-weighted measure, source-density
measure, original volume, or original prior is dominated by the local finite
following-patch source cylinder.  Those are separate source-density/Jacobian
and readback/raw-image handoff tasks.

