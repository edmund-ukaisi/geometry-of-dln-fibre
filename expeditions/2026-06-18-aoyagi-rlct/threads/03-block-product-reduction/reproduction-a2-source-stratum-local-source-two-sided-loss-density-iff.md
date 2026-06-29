# Reproduction - A2 source-stratum/local-source two-sided loss-density iff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised as a boundary-explicit local
coverage wrapper.

## Source Anchor

Aoyagi PDF p. 13 uses a source-rank stratum as the ambient base locus, while a
constructed chart usually gives residual information only on a smaller local
source.  The previous checkpoint gave the source-stratum supplied-bound iff
when residual hypotheses are already available on the whole source-rank
stratum.  The present step keeps the missing coverage statement explicit:
inside a supplied open neighborhood `Ulocal`, the source-rank stratum must be
contained in the supplied `localSource`.

No source coverage, chart image equality, comparison bound, density transport,
normal-crossing, pole-order, or RLCT result is proved here.

## Calculation

Let

```text
S = paperEndpointFixedBaseSourceRankStratum (K := R) W B Cedge r rEdge.
```

Assume an open neighborhood `Ulocal` of `x0` and

```text
Ulocal inter S subset Ulocal inter localSource.
```

Since `Ulocal` is a neighborhood of `x0`,

```text
nhdsWithin x0 (Ulocal inter S) = nhdsWithin x0 S.
```

Thus the four source-stratum-filter bounds can be reused on the local source

```text
source = Ulocal inter S.
```

The residual hypotheses are supplied on `localSource`:

```text
AEMeasurable residualSquareSum (mu.restrict localSource),
residualSquareSum > 0 a.e.,
residualSquareSum <= R^2 a.e.
```

The coverage inclusion gives `source subset localSource`, so these three
residual hypotheses restrict to `mu.restrict source`.

Now apply the local-source two-sided iff to `source = Ulocal inter S`.  If it
returns `Uchart`, set

```text
U = Uchart inter Ulocal.
```

Then

```text
Uchart inter (Ulocal inter S) = U inter S,
```

so the local-source conclusion rewrites to the desired source-stratum
conclusion:

```text
actual loss-density integral over (mu.restrict (U inter S)).prod nu < infinity
iff
residualNegPowerIntegrableOn Cedge (U inter S) mu t.
```

## Lean Shape

Lean formalises this in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

with:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_sourceStratum_bounds_locally_subset_localSource_two_sided_bounds
```

The proof:

1. abbreviates `sourceStratum` and `source := Ulocal inter sourceStratum`;
2. proves the `nhdsWithin` equality using `nhdsWithin_inter_of_mem`;
3. restricts residual `AEMeasurable`, positivity, and `<=R^2` hypotheses from
   `localSource` to `source` using the supplied coverage inclusion;
4. applies the local-source two-sided iff to `source`;
5. rewrites the witness by taking `U := Uchart inter Ulocal`.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

passed.

## Nonclaims

- No proof of the four supplied comparison bounds.
- No proof of residual hypotheses on `localSource`; they are inputs.
- No proof of source-rank-stratum coverage by `localSource`; the local
  coverage inclusion is an input.
- No construction, coverage, or image theorem for Aoyagi's p.13 chart.
- No source-prior, Jacobian, density, or product-measure transport theorem.
- No original-loss identification.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
