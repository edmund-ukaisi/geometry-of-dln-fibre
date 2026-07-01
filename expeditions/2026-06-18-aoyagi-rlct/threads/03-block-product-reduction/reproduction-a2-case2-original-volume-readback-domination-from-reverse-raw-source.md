# A2 Case 2: original-volume readback domination from reverse raw-source domination

Status: checked for formalisation.

## Local objects

Work in the Case 2 passive-theta endpoint chart.  Let

- `sourceChart : Theta -> EdgeFamily`;
- `readback : EdgeFamily -> Theta`;
- `rawMap : Theta -> RawTuple`;
- `rawSourceSet` be the p.13 raw-order source-recursive chart set;
- `sourceRef(V) = Measure.map sourceChart (thetaReference.restrict V)`;
- `originalVolume` be the fixed-basis original edge-family Haar volume.

The available local source-image theorem gives an open neighborhood `V0` of
`z0`, contained in the ambient open set `G`, on which

1. `readback (sourceChart z) = z`;
2. `sourceChart` is injective and continuous on `V0`;
3. `sourceChart '' V0` is measurable;
4. `sourceChart '' V0` lies in the p.13 source set.

The reverse raw-source domination bridge can then be run with ambient set
`V0`, producing a smaller open `V subset V0`.  The four source-chart
properties restrict from `V0` to `V`; measurability of `sourceChart '' V`
follows again from the continuous-on/injective-on image theorem for measurable
sets.

## Calculation

Assume the remaining reverse raw-source comparison on this smaller `V`:

```text
rawHaar.restrict rawSourceSet
  <= D * Measure.map rawMap (thetaReference.restrict V).
```

For any measurable chart piece `C` with `C subset sourceChart '' V`, the p.13
source-set containment gives `C subset p13SourceSet`.  The already proved
original-volume bridge gives

```text
originalVolume.restrict C
  <= ((cHaar^{-1}) * D) * sourceRef(V),
```

where `cHaar` is the scalar comparing the raw-order tuple Haar measure with
`originalTupleVolume`.

Because `readback` is a left inverse to `sourceChart` on `V`,

```text
Measure.map readback sourceRef(V) = thetaReference.restrict V.
```

Since `V subset G`,

```text
Measure.map readback sourceRef(V)
  <= thetaReference.restrict G.
```

Mapping the original-volume domination through `readback` therefore gives

```text
Measure.map readback (originalVolume.restrict C)
  <= ((cHaar^{-1}) * D) * thetaReference.restrict G.
```

The same domination also gives a.e. measurability of `readback` for
`originalVolume.restrict C`, by absolute continuity with respect to
`sourceRef(V)`.

## Nonclaims

This proves only the conditional handoff from reverse raw-source domination to
readback domination.  It does not prove the reverse raw-source domination
itself, determinant-chart Haar transport, raw-Haar pushforward equality,
source-image coverage, source-rank coverage, original source-prior transport,
normal crossings, pole order, or RLCT extraction.
