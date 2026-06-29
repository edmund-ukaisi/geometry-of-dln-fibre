# Review - A2 Case 2 Passive Jacobian-Weighted Source-Stratum Bounds Finite Integral

Date: 2026-06-29.

Status: PASS after one documentation-boundary fix.

## Scope

Reviewed artifacts:

```text
reproduction-a2-case2-passive-jacobian-weighted-source-stratum-bounds-finite-integral.md
statement-card-a2-case2-passive-jacobian-weighted-source-stratum-bounds-finite-integral.md
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Reviewed theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass_sourceStratum_bounds
```

## Source and Boundary Review

Bernoulli the 3rd performed an xhigh read-only source/math fidelity review.
The reviewer found that the reproduction and statement card correctly
distinguish Aoyagi pp. 12-13 p.13 block/product-reduction support from the
repo-added chart-produced passive Jacobian-weighted measure packaging.

One documentation issue was found: the Lean theorem docstring had a weaker
nonclaim caveat than the reproduction and statement card.  It mentioned no
external/original source prior, source-image equality, normal crossings, pole
order, or RLCT, but omitted exact localized residual marginal and
source-rank/source-image coverage.  The docstring was strengthened to say the
theorem does not prove an exact localized residual marginal and does not prove
source-image equality or source-rank coverage.

No formal statement or proof bug was reported.

## Lean/API Review

Kant the 3rd performed an xhigh read-only Lean/API review and reported PASS.
The review confirmed the intended proof route:

- the theorem states loss and density bounds on `nhdsWithin base sourceStratum`;
- the residual-source package is consumed for the chart-produced
  Jacobian-weighted measure;
- finite passive mass is installed only to infer `SFinite muJ`;
- source-stratum measurability is obtained from identity edge-family
  continuity;
- retained-passive local-source coverage is invoked at the fixed base;
- the generic source-stratum-bounds/local-source consumer supplies the final
  finite integral over `muJ.restrict (U inter sourceStratum)`.

## Verification

After the docstring fix, focused build passed:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

The full aggregator build had passed before the docstring-only fix:

```text
scripts/lb DLNFibre
```

Final hygiene checks passed:

```text
git diff --check
scripts/sorries
```

`scripts/sorries` reports:

```text
0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

Direct axiom probe for the theorem reports:

```text
[propext, Classical.choice, Quot.sound]
```

## Verdict

PASS.  The theorem is a chart-produced passive product-domain finite-integral
handoff with source-stratum comparison hypotheses.  It does not prove exact
localized residual marginal, determinant-chart Haar pushforward, raw/source
Haar theorem, original source-prior transport, source-prior Jacobian formula,
source-image equality, source-rank coverage, normal crossings, pole order, or
RLCT.
