# Review - A2 Case 2 baseJ raw-Haar domination from determinant Haar

Date: 2026-07-01.

Status: controller review PASS; xhigh scout reports by Peirce, Arendt, and
Raman were integrated for the boundary around the remaining determinant-chart
domination hypothesis.

## Checks

- The theorem is about `baseJ`, not the unweighted `passiveSource`.
- The formal density in `baseJ` is the same density used on
  `rawHaar.restrict rawDetChart` before applying the retained-passive raw-order
  map.
- The conclusion is

```text
Measure.map rawMap (baseJ.restrict V)
  <= c • rawHaar.restrict rawSourceSet,
```

not the earlier inverse-Jacobian target

```text
c • ((rawHaar.restrict rawSourceSet).withDensity rawInverseJacobianDensity).
```

- The scalar is the same `c`; no local boundedness constant `K` is introduced
  in this theorem.
- The determinant-chart domination hypothesis remains explicit and is still
  about the unweighted `passiveSource`.
- Nothing in the current infrastructure proves that hypothesis for arbitrary
  `passiveMeasure`; singular or atomic passive measures remain possible.

## Boundary

This is conditional measure transport.  It is not exact raw-Haar pushforward
for the unweighted passive source, not passive-product Haar transport, not
raw-Haar normalization, not source-image or source-rank coverage, and not a
normal-crossing, pole-order, or RLCT theorem.
