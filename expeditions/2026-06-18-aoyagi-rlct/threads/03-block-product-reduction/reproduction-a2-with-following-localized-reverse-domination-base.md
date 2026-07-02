# A2 With-Following Localized Reverse Domination Base

## Purpose

The existing reverse-domination theorem transports a hypothesis on
`rawHaar.restrict rawDetChart` to a conclusion on
`rawHaar.restrict rawSourceSet`.  A local endpoint chart cannot justify such a
global hypothesis.  The honest replacement fixes a raw-order patch `P` and
uses the determinant-side patch

```text
endpointPatch = rawDetChart ∩ Phi^{-1}(P).
```

## Calculation

Let

```text
mu = sourceMeasure.restrict V
Phi = topologyTupleEdgeRawOrder
Y = with-following endpoint topology tuple
rawMap z = Phi (Y z)
J y = ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt y)
baseJ = sourceMeasure.withDensity (fun z => J (Y z)).
```

Assume `P subset rawSourceSet` and

```text
rawHaar.restrict endpointPatch ≤ c • Measure.map Y mu.
```

The patch-parametric raw-order COV gives:

```text
Measure.map Phi ((rawHaar.restrict endpointPatch).withDensity J)
  = rawHaar.restrict P.
```

Weight the domination hypothesis by `J` and push forward through `Phi`.  The
left side becomes `rawHaar.restrict P` by the patch COV.  The right side
becomes

```text
c • Measure.map (Phi ∘ Y)
      (mu.withDensity (fun z => J (Y z)))
  = c • Measure.map rawMap (baseJ.restrict V).
```

Thus

```text
rawHaar.restrict P ≤ c • Measure.map rawMap (baseJ.restrict V).
```

## Boundary

The endpoint-patch domination remains a hypothesis.  This theorem does not
prove endpoint-Haar transport, source-density lower bounds, original prior
transport, source-image coverage, normal crossings, pole order, or RLCT.  It
only replaces the global determinant/raw-source COV target by a named local
patch.

## Verification

Focused and full local Lean builds passed:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
The touched Lean-file forbidden-marker scan and `git diff --check` passed.
The direct axiom probe for the new theorem reported:

```text
[propext, Classical.choice, Quot.sound]
```
