# Review - A2 formal-product domination from determinant domination and source-density lower bound

Date: 2026-07-02.

Status: controller review PASS; xhigh scout `Nash` identified the route.

## Checks

- The theorem does not assume formal-product domination directly.  It assumes
  determinant-side reverse domination plus a source-density lower bound, then
  obtains reverse raw-source domination from the existing raw/source package.
- The formal-product theorem is applied with
  `thetaReference = coordinateSourceMeasure.restrict V`, after shrinking to
  `V subset Vformal`.
- The restriction bookkeeping is correct:

```text
(coordinateSourceMeasure.restrict V).restrict Vformal
  = coordinateSourceMeasure.restrict V.
```

- The scalar is the same as in the raw/source package:

```text
Ddet = Cdet * epsilon^{-1}.
```

- The conclusion is only formal-product domination by the chart-produced
  coordinate source reference.  It is not an original-prior theorem.

## Boundary

The determinant-side reverse domination and the lower bound for
`sourceDensity` remain hypotheses.  No determinant Haar transport, exact
raw-Haar pushforward, raw-Haar normalization, source-image/rank coverage,
original source-prior transport, normal crossings, pole order, or RLCT
extraction is claimed.

## Verification

Focused direct elaboration of
`RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean`
passed before this review note was written.  Focused Lake module build also
passed, as did full local `lake build DLNFibre`, `scripts/sorries`, `git diff
--check`, and direct theorem axiom probing.  The theorem reports only
`[propext, Classical.choice, Quot.sound]`.  Xhigh read-only reviewer `Dirac`
passed the theorem-shape and nonclaim-boundary audit.
