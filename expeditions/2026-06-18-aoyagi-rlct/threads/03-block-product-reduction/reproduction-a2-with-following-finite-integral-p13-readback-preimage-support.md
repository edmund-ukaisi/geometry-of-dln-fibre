# A2 with-following finite integral from p.13 readback-preimage support

Status: controller pen-and-paper reproduction before Lean.

Source: Aoyagi pp. 10-13 retained-passive source chart and pp. 19-22
selected-entry Case 2 coordinates.  This note is independent of the
quiver-based paper.  It is local set bookkeeping plus the existing
with-following finite-integral theorem; it does not use the cited
normal-crossing-to-RLCT theorem.

The existing finite-integral theorem gives, after shrinking around a
basepoint `z0`, finite integrability over every measurable chart piece
contained in the actual local image:

```text
chartPiece subset sourceChart '' V.
```

After the p.13 local image equality step, we want a caller-facing version
where the chart-piece support is instead expressed by the p.13 source set and
the readback landing in the returned theta neighborhood:

```text
chartPiece subset p13SourceSet,
chartPiece subset readback^{-1}(V).
```

## Reproduction

First apply the existing finite-integral theorem to the requested open
neighborhood `G`.  This returns an open set `W` with

```text
z0 in W,
W subset G,
finite integrability for every chartPiece subset sourceChart '' W.
```

Now apply the local image equality theorem with the requested neighborhood
specialized to `W`.  It returns an open set `V` with

```text
z0 in V,
V subset W,
readback(sourceChart z) = z for z in V,
sourceChart '' V is measurable,
sourceChart '' V = p13SourceSet inter readback^{-1}(V).
```

Since `V subset W`, we also have `V subset G`.

Thus, for any chart piece satisfying

```text
chartPiece subset p13SourceSet,
chartPiece subset readback^{-1}(V),
```

the equality gives `chartPiece subset sourceChart '' V`.  Since `V subset W`,
we also have `chartPiece subset sourceChart '' W`, and the finite-integral
package returned for `W` applies unchanged.

## Boundary

This proves a local support conversion and finite-integral wrapper for chart
pieces whose readback lands in the returned local theta neighborhood.  It does
not prove that arbitrary p.13 chart pieces have readback in this neighborhood,
does not prove global p.13 coverage, source-rank-stratum coverage, finite
atlas coverage, original-prior transport beyond the existing bounded-density
hypotheses, Haar/Jacobian transport, normal crossings, pole order, or RLCT.
