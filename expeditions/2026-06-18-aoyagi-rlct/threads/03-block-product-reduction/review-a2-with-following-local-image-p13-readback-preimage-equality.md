# Review: A2 with-following local image equality with p.13 readback preimage

Status: xhigh read-only review PASS.

Reviewer: Sagan the 3rd.

Scope reviewed:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
threads/03-block-product-reduction/reproduction-a2-with-following-p13-pointwise-right-inverse.md
```

The reviewer found no formalisation/math inaccuracy or overclaim in the new
diff.  The pointwise theorem is scoped to

```text
X in p13SourceSet
```

plus the selected-entry pivot nonzero hypothesis on the readback.  The local
image theorem is scoped to

```text
sourceChart '' V = p13SourceSet inter readback^{-1}(V)
```

with `V` shrunk inside the requested neighborhood and inside the pivot locus.

The reproduction note states the same boundary and excludes global pivot
coverage, source-rank coverage, source-prior/Haar transport, normal crossings,
pole order, and RLCT.

The reviewer did not run Lean build commands; build verification is the
controller's responsibility for this integration step.
