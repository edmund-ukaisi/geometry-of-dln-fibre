# A2 with-following local image equality with p.13 readback preimage

Status: controller pen-and-paper reproduction before Lean.

Source: Aoyagi pp. 10-13 retained-passive source chart and pp. 19-22
selected-entry Case 2 coordinates.  This note is independent of the
quiver-based paper.  It is elementary coordinate reconstruction and set
bookkeeping; it does not use the cited normal-crossing-to-RLCT theorem.

Let the enlarged with-following endpoint source chart be

```text
sourceChart : theta -> EdgeFamily
```

and let

```text
readback : EdgeFamily -> theta
p13SourceSet : Set EdgeFamily
```

be the corresponding source readback and retained-passive p.13 source set.
For a basepoint `z0` satisfying the determinant-sector and selected-pivot
nonzero hypotheses, start with an arbitrary open neighborhood `G` of `z0`.

The local readback package exports an open pivot neighborhood `Vpivot` of
`z0` such that every `z in Vpivot` has the selected-entry pivot nonzero and
the readback-left-inverse calculation holds on that neighborhood.  Shrink the
requested neighborhood to

```text
Gpivot := G inter Vpivot.
```

The existing local source-image package then returns an open set `V` with

```text
z0 in V,
V subset Gpivot,
detChart(retainedData z) for z in V,
readback(sourceChart z) = z for z in V,
sourceChart is injective and continuous on V,
sourceChart '' V is measurable.
```

Since `V subset Gpivot`, we have both `V subset G` and `V subset Vpivot`.
Thus every `z in V` also satisfies the selected-entry pivot nonzero condition.

We prove

```text
sourceChart '' V = p13SourceSet inter readback^{-1}(V).
```

## Forward inclusion

Take `E in sourceChart '' V`.  Then `E = sourceChart z` for some `z in V`.
The determinant proof on `V` gives a p.13 determinant-chart datum

```text
detData_z := <retainedData z, detChart proof>.
```

By the definition of the enlarged with-following endpoint source chart,
`sourceChart z` is exactly the retained-passive p.13 source chart applied to
`detData_z`.  Therefore

```text
E in p13SourceSet.
```

The local left inverse gives

```text
readback E = readback(sourceChart z) = z,
```

so `readback E in V`.  Hence

```text
E in p13SourceSet inter readback^{-1}(V).
```

## Reverse inclusion

Take

```text
E in p13SourceSet inter readback^{-1}(V).
```

Then `readback E in V`, and since `V subset Vpivot`, the selected-entry pivot
of `readback E` is nonzero.

The pointwise p.13 right-inverse calculation applies to this `E`:

```text
sourceChart(readback E) = E.
```

Thus `E` is in the image of `V`, with witness `readback E in V`.

This proves the equality.

## Boundary

The statement is local and conditional.  It identifies the returned local
image with `p13SourceSet inter readback^{-1}(V)` after shrinking around a
basepoint whose selected pivot is nonzero.

It does not prove that the selected-pivot condition holds globally on the
p.13 source set, does not prove global p.13 source-set coverage, source-rank
coverage, finite atlas coverage, original-prior support, Haar/Jacobian
transport, normal crossings, pole order, or RLCT.
