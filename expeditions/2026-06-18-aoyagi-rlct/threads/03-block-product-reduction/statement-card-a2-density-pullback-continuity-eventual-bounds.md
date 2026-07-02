# Statement Card - A2 density pullback continuity to eventual bounds

## Expected Lean Names

```text
eventually_const_le_of_continuousAt_lt
eventually_le_const_of_continuousAt_lt
eventually_sourceImageDensity_comp_lower_priorDensity_comp_upper_of_continuousAt
```

## Statement Shape

The generic lower-bound helper says:

```text
ContinuousAt f x0 ->
epsilon < f x0 ->
forall-eventually x in nhds x0, epsilon <= f x.
```

Here `f : alpha -> ENNReal`.

The generic upper-bound helper says:

```text
ContinuousAt f x0 ->
f x0 < K ->
forall-eventually x in nhds x0, f x <= K.
```

Here `f : alpha -> Real`.

The paired source/prior helper specializes these to a source chart:

```text
sourceChart : alpha -> beta
sourceImageDensity : beta -> ENNReal
density : beta -> Real
```

and returns the conjunction:

```text
forall-eventually z in nhds z0,
  epsilon <= sourceImageDensity (sourceChart z),

forall-eventually z in nhds z0,
  density (sourceChart z) <= Kprior.
```

## Inputs Used

- `isOpen_Ioi.mem_nhds` for the lower `ENNReal` bound.
- `isOpen_Iio.mem_nhds` for the upper real bound.
- `ContinuousAt` as a neighborhood pullback.
- `le_of_lt` to weaken strict inequalities to non-strict eventual bounds.

## Nonclaims

The theorem does not construct `sourceImageDensity`, does not identify the
original prior density, and does not prove the required continuity or strict
basepoint inequalities.  It only turns those assumptions into the exact
eventual sockets used by the existing full prior-domination wrapper.
