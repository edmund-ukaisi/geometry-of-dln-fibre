# A2 with-following local source-image right inverse

## Claim

For the enlarged with-following Case 2 endpoint source chart, the existing
local left-inverse package can be upgraded on its returned image:

```text
readback(sourceChart z) = z for z in V
```

implies that every edge family already in the local image satisfies

```text
readback E in V,
sourceChart(readback E) = E.
```

Consequently, if an external source-side measure is first restricted to the
measurable local image `sourceChart '' V`, then pulling it back by `readback`
and pushing it forward by `sourceChart` recovers the same restricted external
measure.

## Pen-and-paper check

Let `E in sourceChart '' V`.  By definition of image, choose `z in V` with
`E = sourceChart z`.  The local package gives

```text
readback(sourceChart z) = z.
```

Therefore

```text
readback E = z in V,
sourceChart(readback E) = sourceChart z = E.
```

For the measure identity, set

```text
candidate = map readback (externalMeasure.restrict (sourceChart '' V)).
```

The right-inverse calculation sends every point of the restricted image back
to the same point after applying `sourceChart`.  The same calculation also
shows that `candidate` is supported on `V`.  Since `sourceChart` is continuous
on the measurable set `V`, it is a.e. measurable for `candidate`, and the
standard measure-map bookkeeping yields

```text
candidate.restrict V = candidate,
map sourceChart candidate = externalMeasure.restrict (sourceChart '' V).
```

## Boundary

This is only a two-sided inverse and measure identity over the local image
returned by the source chart.  It does not prove that the image covers the
p.13 source set, covers a source-rank stratum, forms a finite atlas, identifies
an original source prior, transports Haar/Jacobian measure, proves normal
crossings, computes pole order, or extracts an RLCT.
