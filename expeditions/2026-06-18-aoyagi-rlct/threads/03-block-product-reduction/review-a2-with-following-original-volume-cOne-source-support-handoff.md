# Review - A2 With-Following Original-Volume C-One Source-Support Handoff

Date: 2026-07-07.

## Source-Boundary Check

Reviewer: xhigh read-only sidecar `Godel the 2nd`.

Verdict: PASS.  The wrapper is sound and useful as a direct-volume C-one
support conversion theorem.  It uses no new source mathematics: the outer
source-chart package supplies local left-inverse and p.13 image support, and
the existing C-one support bridge converts ordinary image support into
source-cylinder support.

The reviewer noted that the theorem should not try to expose local
source-chart facts from the source-cylinder original-volume theorem, since
that theorem discards them.  The correct route is the two-stage shrink: outer
source-image package, then inner direct volume source-cylinder theorem.

## Lean-Route Check

Reviewer: xhigh read-only sidecar `Franklin the 2nd`.

Verdict: the theorem shape and proof skeleton are correct.  The statement is
the direct prior C-one wrapper with the prior-density branch removed, calling

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_coordinateSourceReference_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower
```

instead of the direct prior theorem.  The expected eta-sensitive points are the
same cloned `hleftV` and `himage_p13V` field-normalization proofs.

## Boundary

The theorem must keep explicit: measurable chart piece, ordinary local
source-chart support, C-one signed-box support, the source-density lower bound
on `baseJ.restrict V`, `eps != 0`, and `eps != infinity`.

It does not prove C-one support, source-cylinder support for arbitrary pieces,
source-density positivity, determinant/raw Haar transport, Haar normalization,
readback domination, finite-integral transfer, source/source-rank coverage,
original-prior domination, normal crossings, pole order, or RLCT.  It does not
use the quiver paper or quiver Lean evidence.
