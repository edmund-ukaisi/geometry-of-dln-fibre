# Review - A2 Case 2 raw-order reference density transport

Date: 2026-07-01.

Status: controller pre-Lean review.

## Checks

- The raw density is assumed a.e. measurable for the named
  `rawOrderReferenceImage`, not for raw Haar.
- The theorem must instantiate the existing raw-density transport bridge with
  `thetaReference = referenceSource`.
- The local theorem itself restricts the theta measure to `V`; do not pass
  `referenceSource.restrict V` as the source measure.
- The proof needs local a.e. measurability of `rawMap` for
  `referenceSource.restrict V`.
- The target source measure is the chart-produced source image, not an
  original source prior.

## Boundary

This is a naming/specialization layer that makes the existing raw-density
transport theorem consume the concrete raw-order reference image.  It does not
prove the density comes from Aoyagi's original prior, and it does not identify
the raw image with Haar.
