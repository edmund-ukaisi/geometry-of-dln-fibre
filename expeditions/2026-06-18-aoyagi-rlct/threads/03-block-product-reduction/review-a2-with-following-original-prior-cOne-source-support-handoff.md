# Review - A2 With-Following Original-Prior C-One Source-Support Handoff

Date: 2026-07-07.

## Source-Boundary Check

Reviewer: xhigh read-only sidecar `Goodall the 2nd`.

Verdict: PASS.  The wrapper is sound as a support-conversion theorem.  The
recommended outer shrink is

```text
exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
```

because it supplies the local readback left-inverse and p.13 image support.
The inner domination theorem remains the direct source-cylinder original-prior
handoff.

The reviewer emphasized that the support conversion must use the final inner
`V`, not just the outer shrink: ordinary support in `sourceChart '' V` plus
C-one signed-box support converts to
`sourceChart '' (V inter sourceCylinder)` by the existing C-one support
bridge.

## Lean-Route Check

Reviewer: xhigh read-only sidecar `Sartre the 2nd`.

Verdict: the theorem shape and proof route are correct.  The proof should:

```text
1. call the p.13 source-image shrink theorem with G;
2. call the direct prior source-cylinder theorem with G := W;
3. inherit left-inverse, injectivity, continuity, measurable image, and p.13
   support from W to the returned V;
4. use the C-one support bridge to build source-cylinder support;
5. call the direct source-cylinder prior package unchanged.
```

The expected Lean friction is only large `let`-block unfolding and tuple-field
eta around `sourceChart`, `readback`, `cOneReadout`, `signedBox`, and
`sourceCylinder`.

## Boundary

The theorem must keep explicit: measurable chart piece, ordinary local
source-chart support, C-one signed-box support, the source-density lower bound
on `baseJ.restrict V`, `eps != 0`, `eps != infinity`, and the prior-density
upper bound on `originalVolume.restrict chartPiece`.

It does not prove C-one support, source-cylinder support for arbitrary pieces,
source-density positivity, prior-density boundedness, determinant/raw Haar
transport, Haar normalization, readback domination, finite-integral transfer,
source/source-rank coverage, normal crossings, pole order, or RLCT.  It does
not use the quiver paper or quiver Lean evidence.
