# Review - A2 With-Following Original-Prior C-One Eventual Pullback Bounds

Date: 2026-07-07.

## Source-Boundary Check

Reviewer: xhigh read-only sidecar `Popper the 2nd`.

Verdict: PASS.  The wrapper is mathematically faithful as a source-boundary
API.  It takes the two supplied `forall eventually z in nhds z0` bounds,
chooses a common open event, shrinks to `G inter Gbounds`, applies the direct
C-one original-prior domination theorem, and derives the needed a.e. lower
and upper density facts from pointwise membership in `sourceChart '' V`.

The reviewer emphasized the preserved assumptions: chart pieces must be
measurable, lie in `sourceChart '' V`, satisfy pointwise C-one signed-box
support, and the caller still supplies `eps != 0` and `eps != infinity` when
using the domination package.

## Lean-Route Check

Reviewer: xhigh read-only sidecar `Bacon the 2nd`.

Verdict: the theorem shape and proof route are correct.  The recommended
skeleton is:

```text
1. unpack the common eventual event by eventually_nhds_iff;
2. set Gshrink = G inter Gbounds;
3. call the direct original-prior C-one theorem with Gshrink;
4. keep V subset G and V subset Gbounds separately;
5. derive the source-image lower bound on sourceChart '' V;
6. derive the pointwise prior-density upper bound on chartPiece;
7. feed the resulting a.e. facts to the direct prior package.
```

Expected Lean friction was limited to let-unfolding around `sourceChart`,
`readback`, and p.13 image support.  The focused file check confirmed that
the needed conversions are mechanical.

## Boundary

The theorem must keep explicit: supplied eventual pullback density bounds,
measurable chart piece, ordinary local source-chart support, C-one signed-box
support, `eps != 0`, and `eps != infinity`.

It does not prove C-one support, source-density positivity, prior-density
boundedness from continuity, determinant/raw Haar transport, Haar
normalization, source/source-rank coverage, source-prior/original-prior
equality, readback domination, finite-integral transfer, normal crossings,
pole order, or RLCT.  It does not use the quiver paper or quiver Lean
evidence.
