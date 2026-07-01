# A2 Case 2: full source-image prior domination from determinant domination

Status: pen-and-paper reproduction checked; Lean target implemented and xhigh
review passed.

## Question

The determinant-domination finite-integral wrappers already prove integrability
on chart pieces contained in `sourceChart '' V`.  The next measure-level target
is stronger and more local: on the whole returned image

```text
I := sourceChart '' V
```

show that the original edge-family prior, restricted to `I`, is dominated by a
finite scalar times the chart-produced coordinate source measure

```text
(Measure.map sourceChart (coordinateSourceMeasure.restrict V)).restrict I.
```

The determinant-side reverse domination, the lower bound for `sourceDensity`,
and the original-prior density upper bound remain explicit hypotheses.

## Calculation

Let

```text
mu := originalEdgeFamilyVolume,
prior := originalEdgeFamilyPrior density,
sourceRef := Measure.map sourceChart (coordinateSourceMeasure.restrict V),
I := sourceChart '' V.
```

The bounded-prior-density lemma gives, from

```text
forall-ae E with respect to mu.restrict I, density E <= Kprior,
```

the domination

```text
prior.restrict I <= ENNReal.ofReal Kprior * mu.restrict I.
```

This statement is still meaningful when `Kprior < 0`: then
`ENNReal.ofReal Kprior = 0`, and the a.e. hypothesis forces the nonnegative
with-density to vanish on the restricted set.

For the volume part, first choose the source-image volume bridge and then choose
the smaller determinant/raw-source package inside it.  The returned set
`V` satisfies:

```text
V subset G,
readback (sourceChart z) = z for z in V,
sourceChart is injective and continuous on V,
MeasurableSet I,
I subset p13SourceSet.
```

Assume on this same `V`:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (passiveSource.restrict V),
Cdet < infinity,
forall-ae z with respect to baseJ.restrict V, epsilon <= sourceDensity z,
epsilon != 0,
epsilon != infinity.
```

The determinant/raw-source package gives

```text
rawHaar.restrict rawSourceSet
  <= (Cdet * epsilon^{-1}) *
     Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

To feed the source-image volume bridge attached to the larger preliminary shrink, use
`thetaReference := coordinateSourceMeasure.restrict V`.  Since the final `V`
is contained in the preliminary shrink,

```text
(coordinateSourceMeasure.restrict V).restrict Vpre =
  coordinateSourceMeasure.restrict V.
```

The source-image volume bridge applied to `chartPiece := I` gives

```text
mu.restrict I <= Dvol * sourceRef,
```

where

```text
Ddet := Cdet * epsilon^{-1},
Dvol := ((cHaar^{-1} : NNReal) : ENNReal) * Ddet.
```

Restricting the right-hand side to the same image gives the local form:

```text
mu.restrict I <= Dvol * sourceRef.restrict I.
```

Composing the prior-density domination with this volume domination yields

```text
prior.restrict I
  <= (ENNReal.ofReal Kprior * Dvol) * sourceRef.restrict I.
```

The scalar is finite because `ENNReal.ofReal Kprior < infinity`, `Cdet <
infinity`, `epsilon != 0`, and the inverse Haar scalar is finite.

## Boundary

This proves a conditional measure-level source-image domination statement.  It
does not prove the determinant-side reverse domination, the lower bound for
`sourceDensity`, the original prior density upper bound, determinant-chart Haar
transport, exact raw-Haar pushforward, raw-Haar normalization, source-image
coverage, source-rank coverage, normal crossings, pole order, or RLCT
extraction.
