# Reproduction - A2 Source-Image Full Product Domination Handoff

Date: 2026-06-30.

Status: pen-and-paper check before Lean.  This is a domination handoff on the
full p.13 product coordinate measure.  It is not a proof of original-prior
transport.

## Question

The source-image Jacobian bridge proves a finite integral over

```text
(sourceImageMeasure.restrict (U ∩ sourceStratum)).prod ν.
```

Can we use this as a socket for a later original/source-prior transport theorem
that produces an external measure on the full product coordinate space?

## Calculation

Let

```text
μprod = (sourceImageMeasure.restrict (U ∩ sourceStratum)).prod ν.
```

The previous theorem gives

```text
∫⁻ z, ofReal ((ball R).indicator
  (fun u =>
    loss (z.1,u) ^ (-(t + regularCount/2)) * 1) z.2) ∂μprod < ∞.
```

The factor `1` is the trivial transported density.  The measure already lives
on the full product coordinate space

```text
EdgeFamily × EuclideanSpace R rhoReg,
```

so it includes the p.13 regular variables.

If an external product-coordinate source measure `mext` satisfies

```text
mext <= Cext • μprod
```

with `Cext < ∞`, then Mathlib measure monotonicity gives

```text
∫⁻ z, f z ∂mext <= ∫⁻ z, f z ∂(Cext • μprod)
               = Cext * ∫⁻ z, f z ∂μprod < ∞.
```

This is exactly `lintegral_lt_top_of_measure_le_smul`.

## Source-Prior Boundary

Xhigh source scout `Kierkegaard` checked Aoyagi pp. 10-13.  The eventual
source-prior theorem should not be passive-theta-only.  Aoyagi's p.13
regular-suspension variables are the regular block variables

```text
B = C1 - I, F2, F3
```

beside the residual chart coordinates.  The pulled-back source prior should
have density

```text
phi(Psi(theta,u)) * |J_Psi(theta,u)|
```

against the product of residual chart measure and Lebesgue measure on the
regular variables.  After shrinking, continuity and nonvanishing should give a
positive finite upper bound and a positive lower bound.

This handoff proves only the downstream consequence of such a transport after
it has been converted to finite-scalar domination by `μprod`.  It does not
prove the chart `Psi`, its readback, the Jacobian identity, Haar transport, or
original-prior density equality.

## Lean Target

Add to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean`:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalProductMeasure_le_smul_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

The theorem should return the same open `W` and a local source open `U`; for
any external product measure dominated by a finite scalar multiple of the
source-image product measure, the finite loss-power integral follows.

## Nonclaims

No original/source prior density identity, no proof that an original prior
satisfies the domination, no passive-theta-only full p.13 prior transport, no
Haar transport, no source-rank coverage, no normal crossings, no pole order,
and no RLCT extraction.
