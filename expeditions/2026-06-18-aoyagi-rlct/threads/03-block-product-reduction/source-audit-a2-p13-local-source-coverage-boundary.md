# Source Audit - A2 p.13 local source coverage boundary

Date: 2026-06-26.

## Question

After the local-source finite-integral consumer landed, the next tempting
claim was that Aoyagi's p.13 product-coordinate family itself proves the
local inclusion needed by that consumer:

```text
Ulocal inter sourceStratum subset Ulocal inter localSource.
```

Equivalently, one might hope that the p.13 displayed coordinates give a local
source chart or inverse covering the source-rank stratum near the base chain.

## Source Check

Aoyagi pp. 10-13 prove an algebraic normal form.  Lemma 2 keeps the invertible
block `A1` and solves

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = A4 - A3 A1^{-1} A2.
```

The inverse formula requires the retained passive block:

```text
A2 = -A1 F2,
A3 = -F3 A1,
A4 = C4 + F3 A1 F2.
```

Theorem 3 recursively applies this block algebra and the p.13 display rewrites
the product difference after triangular multipliers as

```text
[ C1 - I   -F2 ]
[ -F3   prod C^(s) - F3 F2 ].
```

This is a normal-form calculation for the product difference.  The paper does
not state a source-image equality, a finite cover of determinant charts, a
local inverse containing all passive variables, a Jacobian/prior transport
theorem, or a concrete p.13 source-measure pushforward.

## Lean/API Check

The current Lean API matches that boundary:

- forward p.13 product-coordinate source-rank membership is proved;
- small-radius forward membership in the source-rank stratum is proved;
- the explicit local-source finite-integral theorem and the new source-stratum
  consumer both keep the local source or local inclusion supplied;
- selected-entry finite chart-image facts are finite residual-coordinate
  facts, not DLN source coverage;
- raw determinant-chart inverses exist for the full raw one-step chart, but
  the p.13 raw tuple is only a constrained section.

The exact missing hypotheses still appear as `hsourceStratum_local_eq`,
`hsourceStratum_eq`, or the local inclusion into `localSource` in the
downstream measure handoffs.

## Decision

Do not add another wrapper around the source-stratum local-subset consumer as
if it were coverage.  The consumer is the right Lean boundary: it is useful
only after a separate chart/source theorem supplies the local inclusion.

The next source-moving A2 work should be one of:

- prove a genuine source chart theorem with passive variables, inverse,
  source-rank coverage, and density/prior transport;
- prove a smaller reverse rank/readback theorem that moves one obstacle
  without claiming coverage;
- move to a different source-backed finite algebra slice.

## Ledger

Proved: block elimination algebra, product-difference normal form, forward
p.13 source-rank image membership, local raw-section support, section-image
measure identity, and the conditional finite-integral consumer from local
source to locally covered source-rank stratum.

Assumed: any local inclusion from the source-rank stratum into a supplied
local source, any source/image equality, any p.13 source-chart inverse with
passive variables, and any source-measure/density transport.

Cited: only the separate normal-crossing-to-RLCT extraction interface.
Aoyagi pp. 10-13 are source evidence for the displayed algebra, not a Lean
citation for coverage.

Deferred: determinant-chart finite cover, exact-rank/source-rank openness,
local inverse/source coverage, density/Jacobian identity, normal-crossing
construction, pole order, and RLCT.

Nonclaims: no quiver-paper input, no proof of the local inclusion consumed by
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_localSource`,
no raw-Haar pushforward, and no final Aoyagi theorem.
