# Review: A2 with-following finite integral from p.13 readback-preimage support

Status: xhigh read-only review PASS.

Reviewer: Ampere the 3rd.

Scope reviewed:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
threads/03-block-product-reduction/reproduction-a2-with-following-finite-integral-p13-readback-preimage-support.md
```

The reviewer found no blocking formalisation/math inaccuracy or overclaim.
The Lean wrapper returns a shrunk open `V ⊆ G`, requires measurable chart
pieces to satisfy both

```text
chartPiece subset p13SourceSet
chartPiece subset readback^{-1}(V)
```

and uses the local equality

```text
sourceChart '' V = p13SourceSet inter readback^{-1}(V)
```

only to convert these two support assumptions into `chartPiece subset
sourceChart '' V`, then widens along `V subset W` to call the older
finite-integral package.

The review also checked the boundary: no claim that arbitrary p.13 chart
pieces have readback in `V`, no global p.13 coverage, source-rank coverage,
finite atlas, Haar/Jacobian transport, normal crossings, pole order, or RLCT.

Non-blocking issue fixed after review: the initial reproduction note described
the proof order as equality-first, while the Lean proof is finite-first then
equality-shrink.  The reproduction note now matches the Lean proof order.
