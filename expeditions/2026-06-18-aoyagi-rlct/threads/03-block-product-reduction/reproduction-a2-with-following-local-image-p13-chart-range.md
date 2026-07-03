# A2 with-following local image p.13 chart range

## Claim

For the enlarged with-following Case 2 endpoint source chart, the existing
local source-image package returns an open set `V` on which every point has
retained-passive determinant-chart data:

```text
(retainedData z).detChart for z in V.
```

Therefore each local image point is not merely a member of the p.13 source
edge-family set.  It is explicitly in the range of the retained-passive p.13
source chart:

```text
sourceChart z =
  paperEndpointFixedBaseRetainedPassiveP13SourceChart
    ⟨retainedData z, detChart proof⟩.
```

The same statement holds for every `E in sourceChart '' V` by choosing a
preimage `z in V`.

## Pen-and-paper check

Fix `z in V`.  Since `V` is contained in the determinant sector, the retained
data attached to `z` determine a subtype element

```text
data_z := ⟨retainedData z, (retainedData z).detChart⟩.
```

By definition of the with-following endpoint source chart, `sourceChart z` is
the retained-passive p.13 source edge family of that same retained data.
Thus

```text
paperEndpointFixedBaseRetainedPassiveP13SourceChart data_z = sourceChart z.
```

If `E in sourceChart '' V`, choose `z in V` with `E = sourceChart z` and use
the same witness `data_z`.

## Boundary

This is still one-way local image information.  It shows that the image points
already produced by the with-following source chart have explicit p.13 chart
witnesses.  It does not prove the reverse inclusion from p.13 source points
back into the with-following image, global p.13 source-set coverage,
source-rank-stratum coverage, finite atlas coverage, source-prior transport,
Haar/Jacobian transport, normal crossings, pole order, or RLCT.
