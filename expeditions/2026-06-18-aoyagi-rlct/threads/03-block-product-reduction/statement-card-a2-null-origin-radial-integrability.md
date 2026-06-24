# Statement Card - A2 null-origin radial integrability

Date: 2026-06-24.

## Claim

For a nonatomic measure on a normed additive group, the radial
indicator-extensions by zero

```text
x |-> 1_(0,R)(||x||) * phi(||x||)
x |-> 1_(-infinity,R)(||x||) * phi(||x||)
```

agree almost everywhere.  The only possible disagreement is at the origin.

Consequently, for a nontrivial finite-dimensional real normed space with
additive Haar measure, if

```text
R > 0,  a >= 0,  s >= 0,  2s < finrank_R(E),
```

then the nonpunctured radial support

```text
x |-> 1_(-infinity,R)(||x||) * (||x||^2 + a)^(-s)
```

is integrable, and its `ENNReal.ofReal` lower integral is finite.  The same is
true for the equivalent open-ball support `Metric.ball 0 R`.

## Lean Artifacts

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

Theorems:

```text
DLNFibre.DLN.Aoyagi.ae_eq_norm_indicator_Ioo_Iio
DLNFibre.DLN.Aoyagi.integrable_norm_sq_add_rpow_neg_indicator_Iio
DLNFibre.DLN.Aoyagi.lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Iio_lt_top
DLNFibre.DLN.Aoyagi.norm_sq_add_rpow_neg_indicator_ball_eq_indicator_Iio
DLNFibre.DLN.Aoyagi.integrable_norm_sq_add_rpow_neg_indicator_ball
DLNFibre.DLN.Aoyagi.lintegral_ofReal_norm_sq_add_rpow_neg_indicator_ball_lt_top
```

## Proof Ingredients

- `Measure.ae_ne` from `NoAtoms`;
- `x != 0 -> 0 < ||x||`;
- a.e. congruence for `Integrable`;
- `lintegral_congr_ae` for the lower-integral handoff;
- the pointwise identity `x in Metric.ball 0 R iff ||x|| < R`.

## Nonclaims

- No pointwise regularity at the origin.
- No closed-ball theorem or boundary-sphere nullity.
- No endpoint theorem.
- No lower/divergence theorem.
- No uniform asymptotic in `a`.
- No bounded-density or product-coordinate theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT.
